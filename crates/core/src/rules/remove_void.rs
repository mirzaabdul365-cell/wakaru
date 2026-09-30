use swc_core::common::{Mark, Span, Spanned, SyntaxContext};
use swc_core::ecma::ast::{
    ArrowExpr, ArrowFunctionBody, BlockStmt, CatchClause, Class, ClassDecl, Constructor, Decl,
    Expr, FnDecl, FnExpr, ForHead, ForInStmt, ForOfStmt, ForStmt, Function, Ident, ImportSpecifier,
    Lit, Module, ModuleItem, ParamOrTsParamProp, Pat, Stmt, UnaryExpr, UnaryOp, VarDecl,
    VarDeclKind, VarDeclOrExpr, WithStmt,
};
use swc_core::ecma::visit::{Visit, VisitMut, VisitMutWith, VisitWith};

use super::eval_utils::is_direct_eval_call;
use crate::utils::paren::strip_parens;

/// Rewrites `void <number>` to `undefined`, but only where the `undefined`
/// reference it produces provably resolves to the global value.
///
/// `void 0` always evaluates to the real `undefined`, whereas the identifier
/// `undefined` resolves to whatever `undefined` is bound to in scope. The two are
/// only interchangeable where `undefined` is not shadowed. This rewrite is
/// therefore scope-precise: it converts `void <number>` in scopes where
/// `undefined` is the global, and preserves it inside any scope that binds
/// `undefined` — a function parameter, a hoisted `var`/`function`, a block-scoped
/// `let`/`const`/`class`, a `catch` binding, or a module-level declaration — as
/// well as inside a `with` block or a function-like scope that runs direct
/// `eval`, either of which can make `undefined` resolve to something else.
///
/// Shadowing in one scope only protects that scope: `void 0` in an unrelated
/// scope still converts.
pub struct RemoveVoid {
    unresolved_ctxt: SyntaxContext,
    module_shadowed: bool,
    shadow_scopes: Vec<Span>,
}

impl RemoveVoid {
    pub fn new(unresolved_mark: Mark) -> Self {
        Self {
            unresolved_ctxt: SyntaxContext::empty().apply_mark(unresolved_mark),
            module_shadowed: false,
            shadow_scopes: Vec::new(),
        }
    }

    /// Kept for the pipeline call site. The rule is now internally scope-precise,
    /// so it is always safe to run.
    pub fn should_run(_module: &Module) -> bool {
        true
    }

    fn in_shadowed_scope(&self, span: Span) -> bool {
        self.module_shadowed
            || self
                .shadow_scopes
                .iter()
                .any(|scope| scope.lo <= span.lo && span.hi <= scope.hi)
    }
}

impl VisitMut for RemoveVoid {
    fn visit_mut_module(&mut self, module: &mut Module) {
        // A top-level `undefined` binding shadows every scope in the module.
        self.module_shadowed = module_scope_binds_undefined(module);
        if !self.module_shadowed {
            let mut collector = ShadowScopeCollector { scopes: Vec::new() };
            module.visit_with(&mut collector);
            self.shadow_scopes = collector.scopes;
        }
        module.visit_mut_children_with(self);
    }

    fn visit_mut_unary_expr(&mut self, expr: &mut UnaryExpr) {
        // Never touch a `delete` operand.
        if expr.op == UnaryOp::Delete {
            return;
        }
        expr.visit_mut_children_with(self);
    }

    fn visit_mut_expr(&mut self, expr: &mut Expr) {
        expr.visit_mut_children_with(self);

        if let Expr::Unary(UnaryExpr { op, arg, span }) = expr {
            if *op == UnaryOp::Void
                && is_numeric_literal(strip_parens(arg))
                && !self.in_shadowed_scope(*span)
            {
                *expr = Expr::Ident(Ident::new("undefined".into(), *span, self.unresolved_ctxt));
            }
        }
    }
}

fn is_numeric_literal(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(Lit::Num(_)))
}

// --- binding detection -------------------------------------------------------

/// Whether a binding pattern binds an identifier named `undefined`. Default-value
/// expressions inside the pattern are not bindings, so they are skipped.
fn pat_binds_undefined(pat: &Pat) -> bool {
    let mut finder = PatUndefinedFinder { found: false };
    pat.visit_with(&mut finder);
    finder.found
}

struct PatUndefinedFinder {
    found: bool,
}

impl Visit for PatUndefinedFinder {
    fn visit_ident(&mut self, ident: &Ident) {
        if ident.sym == "undefined" {
            self.found = true;
        }
    }
    fn visit_expr(&mut self, _: &Expr) {}
}

/// Finds a `var`/`function` binding named `undefined` within the current function
/// scope: descends through nested blocks and control flow (where `var` hoists)
/// but not into nested function-like or class scopes.
#[derive(Default)]
struct HoistedUndefinedFinder {
    found: bool,
}

impl Visit for HoistedUndefinedFinder {
    fn visit_var_decl(&mut self, decl: &swc_core::ecma::ast::VarDecl) {
        if decl.kind == VarDeclKind::Var {
            for d in &decl.decls {
                if pat_binds_undefined(&d.name) {
                    self.found = true;
                }
            }
        }
        decl.visit_children_with(self);
    }

    fn visit_fn_decl(&mut self, decl: &FnDecl) {
        if decl.ident.sym == "undefined" {
            self.found = true;
        }
    }

    fn visit_function(&mut self, _: &Function) {}
    fn visit_arrow_expr(&mut self, _: &ArrowExpr) {}
    fn visit_class(&mut self, _: &Class) {}
}

/// Whether the immediate statements of a block/function-body level introduce a
/// block-scoped binding named `undefined` (`let`/`const`/`class`). `var`/
/// `function` are function-scoped and handled by `HoistedUndefinedFinder`.
fn stmts_block_bind_undefined(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|stmt| match stmt {
        Stmt::Decl(Decl::Var(decl)) if decl.kind != VarDeclKind::Var => {
            decl.decls.iter().any(|d| pat_binds_undefined(&d.name))
        }
        Stmt::Decl(Decl::Class(ClassDecl { ident, .. })) => ident.sym == "undefined",
        _ => false,
    })
}

/// Whether a function-like scope (params + body) binds `undefined` or runs direct
/// `eval`. Covers parameters, hoisted `var`/`function`, body-top-level `let`/
/// `const`/`class`, and direct `eval`.
fn function_scope_shadows(params: &[Pat], body_stmts: &[Stmt], has_body: bool) -> bool {
    if params.iter().any(pat_binds_undefined) {
        return true;
    }
    if !has_body {
        return scope_has_direct_eval(params, &[]);
    }
    if stmts_block_bind_undefined(body_stmts) {
        return true;
    }
    let mut hoisted = HoistedUndefinedFinder::default();
    body_stmts.visit_with(&mut hoisted);
    if hoisted.found {
        return true;
    }
    scope_has_direct_eval(params, body_stmts)
}

fn scope_has_direct_eval(params: &[Pat], body_stmts: &[Stmt]) -> bool {
    let mut finder = ScopeEvalFinder::default();
    params.visit_with(&mut finder);
    body_stmts.visit_with(&mut finder);
    finder.found
}

/// Whether the module's top-level scope binds `undefined`.
fn module_scope_binds_undefined(module: &Module) -> bool {
    // Import bindings.
    for item in &module.body {
        if let ModuleItem::ModuleDecl(decl) = item {
            let mut imports = ImportUndefinedFinder { found: false };
            decl.visit_with(&mut imports);
            if imports.found {
                return true;
            }
        }
    }
    let stmts: Vec<Stmt> = module
        .body
        .iter()
        .filter_map(|item| match item {
            ModuleItem::Stmt(stmt) => Some(stmt.clone()),
            _ => None,
        })
        .collect();
    if stmts_block_bind_undefined(&stmts) {
        return true;
    }
    let mut hoisted = HoistedUndefinedFinder::default();
    stmts.visit_with(&mut hoisted);
    hoisted.found
}

struct ImportUndefinedFinder {
    found: bool,
}

impl Visit for ImportUndefinedFinder {
    fn visit_import_specifier(&mut self, spec: &ImportSpecifier) {
        let local = match spec {
            ImportSpecifier::Named(s) => &s.local,
            ImportSpecifier::Default(s) => &s.local,
            ImportSpecifier::Namespace(s) => &s.local,
        };
        if local.sym == "undefined" {
            self.found = true;
        }
    }
}

// --- shadow-scope span collection --------------------------------------------

struct ShadowScopeCollector {
    scopes: Vec<Span>,
}

impl Visit for ShadowScopeCollector {
    fn visit_function(&mut self, function: &Function) {
        let params: Vec<Pat> = function.params.iter().map(|p| p.pat.clone()).collect();
        let (stmts, has_body) = match &function.body {
            Some(body) => (body.stmts.clone(), true),
            None => (Vec::new(), false),
        };
        if function_scope_shadows(&params, &stmts, has_body) {
            self.scopes.push(function.span);
        }
        function.visit_children_with(self);
    }

    fn visit_arrow_expr(&mut self, arrow: &ArrowExpr) {
        let params: Vec<Pat> = arrow.params.clone();
        let shadows = match arrow.body.as_ref() {
            ArrowFunctionBody::FunctionBody(body) => {
                function_scope_shadows(&params, &body.stmts, true)
            }
            ArrowFunctionBody::Expr(expr) => {
                if params.iter().any(pat_binds_undefined) {
                    true
                } else {
                    let mut eval = ScopeEvalFinder::default();
                    expr.visit_with(&mut eval);
                    eval.found
                }
            }
        };
        if shadows {
            self.scopes.push(arrow.span);
        }
        arrow.visit_children_with(self);
    }

    fn visit_constructor(&mut self, constructor: &Constructor) {
        let params: Vec<Pat> = constructor
            .params
            .iter()
            .filter_map(|p| match p {
                ParamOrTsParamProp::Param(param) => Some(param.pat.clone()),
                _ => None,
            })
            .collect();
        let (stmts, has_body) = match &constructor.body {
            Some(body) => (body.stmts.clone(), true),
            None => (Vec::new(), false),
        };
        if function_scope_shadows(&params, &stmts, has_body) {
            self.scopes.push(constructor.span);
        }
        constructor.visit_children_with(self);
    }

    fn visit_block_stmt(&mut self, block: &BlockStmt) {
        // Standalone blocks, `if`/loop bodies, `try` blocks, static blocks. (Since
        // swc_core 77 function bodies are not `BlockStmt`, so this never
        // double-counts a function scope.)
        if stmts_block_bind_undefined(&block.stmts) {
            self.scopes.push(block.span);
        }
        block.visit_children_with(self);
    }

    fn visit_catch_clause(&mut self, clause: &CatchClause) {
        if clause.param.as_ref().is_some_and(pat_binds_undefined) {
            self.scopes.push(clause.body.span);
        }
        clause.visit_children_with(self);
    }

    fn visit_fn_expr(&mut self, fn_expr: &FnExpr) {
        // A named function expression binds its own name inside its scope
        // (`const f = function undefined() { ... }`), so `undefined` there refers
        // to the function, not the global.
        if fn_expr
            .ident
            .as_ref()
            .is_some_and(|id| id.sym == "undefined")
        {
            self.scopes.push(fn_expr.function.span);
        }
        fn_expr.visit_children_with(self);
    }

    fn visit_for_stmt(&mut self, node: &ForStmt) {
        if matches!(&node.init, Some(VarDeclOrExpr::VarDecl(decl)) if vardecl_binds_undefined(decl))
        {
            self.scopes.push(node.span);
        }
        node.visit_children_with(self);
    }

    fn visit_for_in_stmt(&mut self, node: &ForInStmt) {
        if for_head_binds_undefined(&node.left) {
            self.scopes.push(node.span);
        }
        node.visit_children_with(self);
    }

    fn visit_for_of_stmt(&mut self, node: &ForOfStmt) {
        if for_head_binds_undefined(&node.left) {
            self.scopes.push(node.span);
        }
        node.visit_children_with(self);
    }

    fn visit_with_stmt(&mut self, stmt: &WithStmt) {
        // Inside `with`, `undefined` may resolve to a property of the object.
        self.scopes.push(stmt.body.span());
        stmt.visit_children_with(self);
    }
}

fn vardecl_binds_undefined(decl: &VarDecl) -> bool {
    decl.decls.iter().any(|d| pat_binds_undefined(&d.name))
}

/// Whether a `for (… in/of …)` head declares a binding named `undefined`
/// (`for (let undefined of xs)`). A bare target that is not a declaration
/// assigns to an existing binding and introduces nothing new.
fn for_head_binds_undefined(head: &ForHead) -> bool {
    matches!(head, ForHead::VarDecl(decl) if vardecl_binds_undefined(decl))
}

/// Finds a direct `eval(...)` within a single scope, not descending into nested
/// function-like scopes.
#[derive(Default)]
struct ScopeEvalFinder {
    found: bool,
}

impl Visit for ScopeEvalFinder {
    fn visit_call_expr(&mut self, call: &swc_core::ecma::ast::CallExpr) {
        if is_direct_eval_call(call) {
            self.found = true;
            return;
        }
        call.visit_children_with(self);
    }
    fn visit_function(&mut self, _: &Function) {}
    fn visit_arrow_expr(&mut self, _: &ArrowExpr) {}
    fn visit_constructor(&mut self, _: &Constructor) {}
}
