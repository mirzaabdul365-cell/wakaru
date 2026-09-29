use std::collections::HashSet;

use swc_core::atoms::Atom;
use swc_core::common::{Mark, Span, SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::{
    ArrowExpr, AssignExpr, AssignTarget, Callee, Constructor, Expr, Function, MemberProp, Module,
    ObjectLit, ObjectPatProp, Pat, Prop, PropName, PropOrSpread, SimpleAssignTarget, SpreadElement,
    StaticBlock, UpdateExpr, VarDeclKind,
};
use swc_core::ecma::visit::{Visit, VisitMut, VisitMutWith, VisitWith};

use super::eval_utils::is_direct_eval_call;

type BindingId = (Atom, SyntaxContext);

/// Converts safe `Object.assign({}, source1, source2, ...)` patterns into object
/// spread syntax.
///
/// Only fires when the **first** argument is a safe object literal target. In
/// that case the semantics are identical: a fresh object is created with the
/// target's own data properties and the sources merged in order.
///
/// ```js
/// // input
/// Object.assign({}, defaults, { extra: 1 })
/// // output
/// { ...defaults, extra: 1 }
/// ```
///
/// The rewrite is binding-aware. It fires only when the `Object` reference is
/// provably the built-in global — the unresolved global binding, or a stable
/// `const` alias of it (`const O = Object; O.assign(...)`) — and never when
/// `Object` or `Object.assign` is reassigned anywhere in the module, when the
/// call sits inside a `with` block, or inside a function-like scope that
/// performs a direct `eval` (either can rebind `Object` dynamically).
pub struct ObjectAssignSpread {
    unresolved_mark: Mark,
    object_mutated: bool,
    object_aliases: HashSet<BindingId>,
    assign_aliases: HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: Vec<Span>,
}

impl ObjectAssignSpread {
    pub fn new(unresolved_mark: Mark) -> Self {
        Self {
            unresolved_mark,
            object_mutated: false,
            object_aliases: HashSet::new(),
            assign_aliases: HashSet::new(),
            with_depth: 0,
            top_level_direct_eval: false,
            direct_eval_scopes: Vec::new(),
        }
    }

    fn call_in_direct_eval_scope(&self, span: Span) -> bool {
        self.top_level_direct_eval
            || self
                .direct_eval_scopes
                .iter()
                .any(|scope| scope.lo <= span.lo && span.hi <= scope.hi)
    }

    /// Whether `callee` names `<Object>.assign` for a provably-global `Object`.
    fn callee_is_object_assign(&self, callee: &Callee) -> bool {
        let Callee::Expr(callee_expr) = callee else {
            return false;
        };
        match callee_expr.as_ref() {
            // `Object.assign(...)` or `O.assign(...)` where O is a stable alias.
            Expr::Member(member) => {
                if !matches!(&member.prop, MemberProp::Ident(i) if i.sym == "assign") {
                    return false;
                }
                let Expr::Ident(obj) = member.obj.as_ref() else {
                    return false;
                };
                let is_global = obj.sym == "Object" && obj.ctxt.outer() == self.unresolved_mark;
                let is_alias = self.object_aliases.contains(&(obj.sym.clone(), obj.ctxt));
                is_global || is_alias
            }
            // Detached method reference: `const a = Object.assign; a(...)` or
            // `const { assign } = Object; assign(...)`. `Object.assign` reads its
            // target and sources from arguments and ignores its `this`, so a
            // detached call is equivalent to the member call.
            Expr::Ident(callee_ident) => self
                .assign_aliases
                .contains(&(callee_ident.sym.clone(), callee_ident.ctxt)),
            _ => false,
        }
    }
}

impl VisitMut for ObjectAssignSpread {
    fn visit_mut_module(&mut self, module: &mut Module) {
        self.object_mutated = object_binding_is_mutated(module, self.unresolved_mark);
        let aliases = if self.object_mutated {
            Aliases::default()
        } else {
            collect_aliases(module, self.unresolved_mark)
        };
        self.object_aliases = aliases.object;
        self.assign_aliases = aliases.assign;
        let eval_scopes = collect_direct_eval_scopes(module);
        self.top_level_direct_eval = eval_scopes.top_level;
        self.direct_eval_scopes = eval_scopes.functions;
        module.visit_mut_children_with(self);
    }

    fn visit_mut_with_stmt(&mut self, stmt: &mut swc_core::ecma::ast::WithStmt) {
        stmt.obj.visit_mut_with(self);
        self.with_depth += 1;
        stmt.body.visit_mut_with(self);
        self.with_depth -= 1;
    }

    fn visit_mut_expr(&mut self, expr: &mut Expr) {
        // Bottom-up: transform inner Object.assign calls first so that their
        // results (plain object literals) can be inlined by an outer transform.
        expr.visit_mut_children_with(self);

        if self.object_mutated || self.with_depth > 0 {
            return;
        }

        let Expr::Call(call) = expr else {
            return;
        };
        if !self.callee_is_object_assign(&call.callee) || self.call_in_direct_eval_scope(call.span)
        {
            return;
        }

        if let Some(new_expr) = transform_object_assign(call.span, &call.args) {
            *expr = new_expr;
        }
    }
}

fn transform_object_assign(span: Span, args: &[swc_core::ecma::ast::ExprOrSpread]) -> Option<Expr> {
    // Need at least one argument (the target)
    let first_arg = args.first()?;
    if first_arg.spread.is_some() {
        return None;
    }
    let Expr::Object(first_obj) = first_arg.expr.as_ref() else {
        return None;
    };
    if !is_safe_to_inline_props(&first_obj.props) {
        return None;
    }

    // Build the spread properties from the remaining arguments.
    //
    // Inline only plain data properties. Accessors, methods, and bare
    // `__proto__` entries are kept behind a spread because directly placing them
    // in the output object literal would change semantics.
    let mut props: Vec<PropOrSpread> = first_obj.props.clone();
    for arg in &args[1..] {
        if arg.spread.is_some() {
            // Can't handle a spread argument in call position — bail out.
            return None;
        }
        if let Expr::Object(obj) = arg.expr.as_ref() {
            if is_safe_to_inline_props(&obj.props) {
                props.extend(obj.props.clone());
                continue;
            }
        }

        props.push(PropOrSpread::Spread(SpreadElement {
            dot3_token: DUMMY_SP,
            expr: arg.expr.clone(),
        }));
    }

    Some(Expr::Object(ObjectLit { span, props }))
}

fn is_safe_to_inline_props(props: &[PropOrSpread]) -> bool {
    props.iter().all(is_safe_to_inline_prop)
}

fn is_safe_to_inline_prop(prop: &PropOrSpread) -> bool {
    match prop {
        PropOrSpread::Spread(_) => true,
        PropOrSpread::Prop(prop) => match prop.as_ref() {
            Prop::Shorthand(ident) => ident.sym != "__proto__",
            Prop::KeyValue(kv) => !is_bare_proto_name(&kv.key),
            Prop::Assign(assign) => assign.key.sym != "__proto__",
            Prop::Getter(_) | Prop::Setter(_) | Prop::Method(_) => false,
        },
    }
}

fn is_bare_proto_name(name: &PropName) -> bool {
    match name {
        PropName::Ident(ident) => ident.sym == "__proto__",
        PropName::Str(value) => value.value == "__proto__",
        PropName::Num(_) | PropName::BigInt(_) | PropName::Computed(_) => false,
    }
}

/// Collect `const X = Object` bindings, where `Object` is the unresolved global.
/// `const` guarantees `X` is never reassigned; `SyntaxContext` on the recorded
/// binding keeps a shadowing inner `X` from matching a different scope's alias.
#[derive(Default)]
struct Aliases {
    object: HashSet<BindingId>,
    assign: HashSet<BindingId>,
}

fn collect_aliases(module: &Module, unresolved_mark: Mark) -> Aliases {
    let mut collector = AliasCollector {
        unresolved_mark,
        aliases: Aliases::default(),
    };
    module.visit_with(&mut collector);
    collector.aliases
}

struct AliasCollector {
    unresolved_mark: Mark,
    aliases: Aliases,
}

impl AliasCollector {
    fn is_global_object(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Ident(id)
            if id.sym == "Object" && id.ctxt.outer() == self.unresolved_mark)
    }
}

impl Visit for AliasCollector {
    fn visit_var_decl(&mut self, decl: &swc_core::ecma::ast::VarDecl) {
        if decl.kind == VarDeclKind::Const {
            for declarator in &decl.decls {
                let Some(init) = &declarator.init else {
                    continue;
                };
                match &declarator.name {
                    // `const O = Object` (object alias) or
                    // `const a = Object.assign` (detached method alias).
                    Pat::Ident(name) => {
                        if self.is_global_object(init) {
                            self.aliases
                                .object
                                .insert((name.id.sym.clone(), name.id.ctxt));
                        } else if is_object_assign_member(init, self.unresolved_mark) {
                            self.aliases
                                .assign
                                .insert((name.id.sym.clone(), name.id.ctxt));
                        }
                    }
                    // `const { assign } = Object` / `const { assign: local } = Object`.
                    Pat::Object(obj_pat) if self.is_global_object(init) => {
                        for prop in &obj_pat.props {
                            if let Some(local) = destructured_assign_binding(prop) {
                                self.aliases.assign.insert(local);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        decl.visit_children_with(self);
    }
}

/// Whether `expr` is exactly `Object.assign` for the unresolved global `Object`.
fn is_object_assign_member(expr: &Expr, unresolved_mark: Mark) -> bool {
    let Expr::Member(member) = expr else {
        return false;
    };
    matches!(&member.prop, MemberProp::Ident(i) if i.sym == "assign")
        && matches!(member.obj.as_ref(), Expr::Ident(id)
            if id.sym == "Object" && id.ctxt.outer() == unresolved_mark)
}

/// For a property in an object-destructuring pattern applied to `Object`, return
/// the local binding id when the source key is `assign` and it binds a plain
/// identifier (`{ assign }` or `{ assign: local }`). Defaulted or nested targets
/// are ignored.
fn destructured_assign_binding(prop: &ObjectPatProp) -> Option<BindingId> {
    match prop {
        ObjectPatProp::Assign(assign) if assign.value.is_none() && assign.key.sym == "assign" => {
            Some((assign.key.sym.clone(), assign.key.ctxt))
        }
        ObjectPatProp::KeyValue(kv) => {
            let key_is_assign = match &kv.key {
                PropName::Ident(i) => i.sym == "assign",
                PropName::Str(s) => s.value == "assign",
                _ => false,
            };
            if !key_is_assign {
                return None;
            }
            match kv.value.as_ref() {
                Pat::Ident(local) => Some((local.id.sym.clone(), local.id.ctxt)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether the global `Object` binding, or its `.assign` property, is written
/// anywhere in the module (`Object = ...`, `Object.assign = ...`, `Object++`).
/// Any such mutation makes every `Object.assign` recovery unsafe module-wide.
fn object_binding_is_mutated(module: &Module, unresolved_mark: Mark) -> bool {
    let mut finder = MutationFinder {
        unresolved_mark,
        mutated: false,
    };
    module.visit_with(&mut finder);
    finder.mutated
}

struct MutationFinder {
    unresolved_mark: Mark,
    mutated: bool,
}

impl MutationFinder {
    fn is_global_object(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Ident(id)
            if id.sym == "Object" && id.ctxt.outer() == self.unresolved_mark)
    }
}

impl Visit for MutationFinder {
    fn visit_assign_expr(&mut self, expr: &AssignExpr) {
        if let AssignTarget::Simple(target) = &expr.left {
            let writes_object = match target {
                SimpleAssignTarget::Ident(ident) => {
                    ident.id.sym == "Object" && ident.id.ctxt.outer() == self.unresolved_mark
                }
                SimpleAssignTarget::Member(member) => {
                    self.is_global_object(member.obj.as_ref())
                        && matches!(&member.prop, MemberProp::Ident(i) if i.sym == "assign")
                }
                _ => false,
            };
            if writes_object {
                self.mutated = true;
            }
        }
        expr.visit_children_with(self);
    }

    fn visit_update_expr(&mut self, expr: &UpdateExpr) {
        if self.is_global_object(expr.arg.as_ref()) {
            self.mutated = true;
        }
        expr.visit_children_with(self);
    }
}

struct DirectEvalScopes {
    top_level: bool,
    functions: Vec<Span>,
}

/// Finds a direct `eval(...)` call within a single scope, without descending
/// into nested function-like scopes (those are their own scopes).
#[derive(Default)]
struct DirectEvalFinder {
    found: bool,
}

impl Visit for DirectEvalFinder {
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
    fn visit_static_block(&mut self, _: &StaticBlock) {}
}

struct DirectEvalScopeCollector {
    functions: Vec<Span>,
}

impl Visit for DirectEvalScopeCollector {
    fn visit_function(&mut self, function: &Function) {
        let mut finder = DirectEvalFinder::default();
        function.params.visit_with(&mut finder);
        function.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(function.span);
        }
        function.visit_children_with(self);
    }

    fn visit_arrow_expr(&mut self, arrow: &ArrowExpr) {
        let mut finder = DirectEvalFinder::default();
        arrow.params.visit_with(&mut finder);
        arrow.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(arrow.span);
        }
        arrow.visit_children_with(self);
    }

    fn visit_constructor(&mut self, constructor: &Constructor) {
        let mut finder = DirectEvalFinder::default();
        constructor.params.visit_with(&mut finder);
        if let Some(body) = &constructor.body {
            body.visit_with(&mut finder);
        }
        if finder.found {
            self.functions.push(constructor.span);
        }
        constructor.visit_children_with(self);
    }

    fn visit_static_block(&mut self, block: &StaticBlock) {
        let mut finder = DirectEvalFinder::default();
        block.body.stmts.visit_with(&mut finder);
        if finder.found {
            self.functions.push(block.span);
        }
        block.visit_children_with(self);
    }
}

fn collect_direct_eval_scopes(module: &Module) -> DirectEvalScopes {
    let mut top_level = DirectEvalFinder::default();
    module.visit_with(&mut top_level);

    let mut collector = DirectEvalScopeCollector {
        functions: Vec::new(),
    };
    module.visit_with(&mut collector);

    DirectEvalScopes {
        top_level: top_level.found,
        functions: collector.functions,
    }
}
