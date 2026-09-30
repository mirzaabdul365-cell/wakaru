use std::collections::HashSet;

use swc_core::atoms::Atom;
use swc_core::common::{Mark, Span, Spanned, SyntaxContext};
use swc_core::ecma::ast::{
    ArrowExpr, AssignExpr, AssignTarget, AutoAccessor, BinaryOp, Callee, ClassProp, Constructor,
    Expr, Function, GetterProp, Lit, MemberExpr, MemberProp, Module, ObjectPatProp, Pat,
    PrivateProp, PropName, SetterProp, SimpleAssignTarget, StaticBlock, UpdateExpr, VarDeclKind,
};
use swc_core::ecma::utils::ExprFactory;
use swc_core::ecma::visit::{Visit, VisitMut, VisitMutWith, VisitWith};

use super::eval_utils::is_direct_eval_call;

type BindingId = (Atom, SyntaxContext);

/// Converts `Math.pow(a, b)` → `a ** b`.
///
/// The rewrite is binding-aware and fires only when the `Math.pow` reference is
/// provably the built-in. It recognises several equivalent spellings:
///
/// - the unresolved global `Math`: `Math.pow(a, b)` and `Math["pow"](a, b)`;
/// - `globalThis.Math`: `globalThis.Math.pow(a, b)` (only the literal
///   `globalThis`, which is the sole cross-environment alias of the global
///   object — `window`/`self` are not);
/// - a stable `const` alias of `Math`, transitively (`const M = Math; const N =
///   M; N.pow(a, b)`), including an alias of `globalThis.Math`;
/// - a detached `const` alias of the method itself (`const p = Math.pow`,
///   `const { pow } = Math`, `const { pow: p } = M`), because `Math.pow` reads
///   both operands from its arguments and ignores its `this`.
///
/// It never fires when the `Math.pow` slot is reassigned anywhere in the module
/// (`Math = ...`, `Math.pow = ...`, `Math["pow"] = ...`, `globalThis.Math = ...`,
/// `M.pow = ...` through an alias, `Math++`), when `globalThis` itself is
/// reassigned (disables only the `globalThis.Math` spelling), when the call sits
/// inside a `with` block, or inside a scope that runs direct `eval`. Every
/// function-like scope is independent: functions, arrows, constructors, getters,
/// setters, and class field / private-field / auto-accessor initializers each
/// isolate their own `eval`, so `eval` in one does not block conversions in
/// another.
pub struct Exponent {
    unresolved_mark: Mark,
    math_slot_mutated: bool,
    globalthis_mutated: bool,
    math_aliases: HashSet<BindingId>,
    pow_aliases: HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: Vec<Span>,
}

impl Exponent {
    pub fn new(unresolved_mark: Mark) -> Self {
        Self {
            unresolved_mark,
            math_slot_mutated: false,
            globalthis_mutated: false,
            math_aliases: HashSet::new(),
            pow_aliases: HashSet::new(),
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

    fn is_unresolved_global(&self, expr: &Expr, name: &str) -> bool {
        matches!(expr, Expr::Ident(id)
            if id.sym == name && id.ctxt.outer() == self.unresolved_mark)
    }

    /// Whether `expr` denotes the built-in `Math` object: the global `Math`, a
    /// tracked `const` alias of it, or `globalThis.Math` (unless `globalThis` was
    /// reassigned).
    fn is_math_object(&self, expr: &Expr) -> bool {
        if self.is_unresolved_global(expr, "Math") {
            return true;
        }
        if let Expr::Ident(id) = expr {
            if self.math_aliases.contains(&(id.sym.clone(), id.ctxt)) {
                return true;
            }
        }
        if let Expr::Member(member) = expr {
            if prop_is(&member.prop, "Math")
                && !self.globalthis_mutated
                && self.is_unresolved_global(member.obj.as_ref(), "globalThis")
            {
                return true;
            }
        }
        false
    }

    /// Whether `callee` names `Math.pow` for a provably-built-in `Math`.
    fn callee_is_math_pow(&self, callee: &Callee) -> bool {
        let Callee::Expr(callee_expr) = callee else {
            return false;
        };
        match callee_expr.as_ref() {
            // `<math>.pow(...)` / `<math>["pow"](...)` where `<math>` is built-in.
            Expr::Member(member) => {
                prop_is(&member.prop, "pow") && self.is_math_object(member.obj.as_ref())
            }
            // Detached method reference: `const p = Math.pow; p(...)`.
            Expr::Ident(callee_ident) => self
                .pow_aliases
                .contains(&(callee_ident.sym.clone(), callee_ident.ctxt)),
            _ => false,
        }
    }
}

impl VisitMut for Exponent {
    fn visit_mut_module(&mut self, module: &mut Module) {
        // Aliases are independent of mutation, so collect them first; the
        // mutation scan then uses them to catch writes through an alias
        // (`const M = Math; M.pow = ...`).
        let aliases = collect_aliases(module, self.unresolved_mark);
        self.math_aliases = aliases.math;
        self.pow_aliases = aliases.pow;

        let mutation = scan_mutations(module, self.unresolved_mark, &self.math_aliases);
        self.math_slot_mutated = mutation.slot;
        self.globalthis_mutated = mutation.globalthis;
        if self.math_slot_mutated {
            // A reassigned `Math.pow` slot makes every spelling unsafe.
            self.math_aliases.clear();
            self.pow_aliases.clear();
        }

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
        // Bottom-up: transform inner `Math.pow` calls first so a nested power
        // becomes the left operand of the outer `**`.
        expr.visit_mut_children_with(self);

        if self.math_slot_mutated || self.with_depth > 0 {
            return;
        }

        let Expr::Call(call) = expr else {
            return;
        };

        // Must have exactly 2 args with no spread.
        if call.args.len() != 2 || call.args[0].spread.is_some() || call.args[1].spread.is_some() {
            return;
        }

        if !self.callee_is_math_pow(&call.callee) || self.call_in_direct_eval_scope(call.span) {
            return;
        }

        let Expr::Call(mut call_owned) = std::mem::replace(expr, Expr::Invalid(Default::default()))
        else {
            unreachable!()
        };
        let b = *call_owned.args.pop().unwrap().expr;
        let a = *call_owned.args.pop().unwrap().expr;

        *expr = a.make_bin(BinaryOp::Exp, b);
    }
}

/// Whether a member property is the identifier or the string-literal `name`
/// (`.pow` and `["pow"]` are equivalent; a computed non-literal or private name
/// is not).
fn prop_is(prop: &MemberProp, name: &str) -> bool {
    match prop {
        MemberProp::Ident(ident) => ident.sym == name,
        MemberProp::Computed(computed) => {
            matches!(computed.expr.as_ref(), Expr::Lit(Lit::Str(s)) if s.value == name)
        }
        MemberProp::PrivateName(_) => false,
    }
}

/// Collect stable `const` aliases of `Math` and of the `Math.pow` method. `const`
/// guarantees the alias is never reassigned; the recorded `SyntaxContext` keeps a
/// shadowing inner binding of the same name from matching a different scope's
/// alias. Runs to a fixpoint so alias-of-alias chains resolve.
#[derive(Default)]
struct Aliases {
    math: HashSet<BindingId>,
    pow: HashSet<BindingId>,
}

fn collect_aliases(module: &Module, unresolved_mark: Mark) -> Aliases {
    let mut aliases = Aliases::default();
    loop {
        // Scope the collector so its immutable borrow of `aliases` is released
        // before we merge its findings back in.
        let (added_math, added_pow) = {
            let mut collector = AliasCollector {
                unresolved_mark,
                aliases: &aliases,
                added_math: HashSet::new(),
                added_pow: HashSet::new(),
            };
            module.visit_with(&mut collector);
            (collector.added_math, collector.added_pow)
        };
        let mut changed = false;
        for id in added_math {
            changed |= aliases.math.insert(id);
        }
        for id in added_pow {
            changed |= aliases.pow.insert(id);
        }
        if !changed {
            break;
        }
    }
    aliases
}

struct AliasCollector<'a> {
    unresolved_mark: Mark,
    aliases: &'a Aliases,
    added_math: HashSet<BindingId>,
    added_pow: HashSet<BindingId>,
}

impl AliasCollector<'_> {
    fn is_unresolved_global(&self, expr: &Expr, name: &str) -> bool {
        matches!(expr, Expr::Ident(id)
            if id.sym == name && id.ctxt.outer() == self.unresolved_mark)
    }

    /// Built-in `Math` object per already-known aliases (grows across fixpoint
    /// rounds): global `Math`, a known alias, or `globalThis.Math`.
    fn is_math_object(&self, expr: &Expr) -> bool {
        if self.is_unresolved_global(expr, "Math") {
            return true;
        }
        if let Expr::Ident(id) = expr {
            if self.aliases.math.contains(&(id.sym.clone(), id.ctxt))
                || self.added_math.contains(&(id.sym.clone(), id.ctxt))
            {
                return true;
            }
        }
        if let Expr::Member(member) = expr {
            if prop_is(&member.prop, "Math")
                && self.is_unresolved_global(member.obj.as_ref(), "globalThis")
            {
                return true;
            }
        }
        false
    }

    /// `<math>.pow` / `<math>["pow"]` for a built-in `<math>`.
    fn is_math_pow_method(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Member(member)
            if prop_is(&member.prop, "pow") && self.is_math_object(member.obj.as_ref()))
    }
}

impl Visit for AliasCollector<'_> {
    fn visit_var_decl(&mut self, decl: &swc_core::ecma::ast::VarDecl) {
        if decl.kind == VarDeclKind::Const {
            for declarator in &decl.decls {
                let Some(init) = &declarator.init else {
                    continue;
                };
                match &declarator.name {
                    Pat::Ident(name) => {
                        let id = (name.id.sym.clone(), name.id.ctxt);
                        if self.is_math_object(init) {
                            // `const M = Math` / `const N = M` / `const M = globalThis.Math`.
                            self.added_math.insert(id);
                        } else if self.is_math_pow_method(init) {
                            // `const p = Math.pow` / `const p = M.pow`.
                            self.added_pow.insert(id);
                        } else if let Expr::Ident(src) = init.as_ref() {
                            // `const q = p` where `p` is a detached method alias.
                            let src_id = (src.sym.clone(), src.ctxt);
                            if self.aliases.pow.contains(&src_id)
                                || self.added_pow.contains(&src_id)
                            {
                                self.added_pow.insert(id);
                            }
                        }
                    }
                    // `const { pow } = Math` / `const { pow: local } = M`.
                    Pat::Object(obj_pat) if self.is_math_object(init) => {
                        for prop in &obj_pat.props {
                            if let Some(local) = destructured_pow_binding(prop) {
                                self.added_pow.insert(local);
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

/// For a property in an object-destructuring pattern applied to `Math`, return
/// the local binding id when the source key is `pow` and it binds a plain
/// identifier (`{ pow }` or `{ pow: local }`).
fn destructured_pow_binding(prop: &ObjectPatProp) -> Option<BindingId> {
    match prop {
        ObjectPatProp::Assign(assign) if assign.value.is_none() && assign.key.sym == "pow" => {
            Some((assign.key.sym.clone(), assign.key.ctxt))
        }
        ObjectPatProp::KeyValue(kv) => {
            let key_is_pow = match &kv.key {
                PropName::Ident(i) => i.sym == "pow",
                PropName::Str(s) => s.value == "pow",
                _ => false,
            };
            if !key_is_pow {
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

#[derive(Default)]
struct Mutation {
    slot: bool,
    globalthis: bool,
}

/// Scan for writes that make recovery unsafe. `slot` covers any write to the
/// `Math.pow` slot itself (`Math = `, `Math.pow = `, `Math["pow"] = `,
/// `globalThis.Math = `, `M.pow = ` through an alias, `Math++`); it disables all
/// recovery. `globalthis` covers reassigning the `globalThis` binding; it only
/// disables the `globalThis.Math` spelling.
fn scan_mutations(
    module: &Module,
    unresolved_mark: Mark,
    math_aliases: &HashSet<BindingId>,
) -> Mutation {
    let mut finder = MutationFinder {
        unresolved_mark,
        math_aliases,
        mutation: Mutation::default(),
    };
    module.visit_with(&mut finder);
    finder.mutation
}

struct MutationFinder<'a> {
    unresolved_mark: Mark,
    math_aliases: &'a HashSet<BindingId>,
    mutation: Mutation,
}

impl MutationFinder<'_> {
    fn is_unresolved_global(&self, expr: &Expr, name: &str) -> bool {
        matches!(expr, Expr::Ident(id)
            if id.sym == name && id.ctxt.outer() == self.unresolved_mark)
    }

    /// Structural built-in `Math` check for write targets (global `Math`, a known
    /// alias, or `globalThis.Math` regardless of `globalThis` reassignment — a
    /// write to that slot is unsafe either way).
    fn target_is_math_object(&self, expr: &Expr) -> bool {
        if self.is_unresolved_global(expr, "Math") {
            return true;
        }
        if let Expr::Ident(id) = expr {
            if self.math_aliases.contains(&(id.sym.clone(), id.ctxt)) {
                return true;
            }
        }
        if let Expr::Member(member) = expr {
            if prop_is(&member.prop, "Math")
                && self.is_unresolved_global(member.obj.as_ref(), "globalThis")
            {
                return true;
            }
        }
        false
    }

    fn note_member_write(&mut self, member: &MemberExpr) {
        // `<math>.pow = ...` / `<math>["pow"] = ...`.
        if prop_is(&member.prop, "pow") && self.target_is_math_object(member.obj.as_ref()) {
            self.mutation.slot = true;
        }
        // `globalThis.Math = ...`.
        if prop_is(&member.prop, "Math")
            && self.is_unresolved_global(member.obj.as_ref(), "globalThis")
        {
            self.mutation.slot = true;
        }
    }
}

impl Visit for MutationFinder<'_> {
    fn visit_assign_expr(&mut self, expr: &AssignExpr) {
        if let AssignTarget::Simple(target) = &expr.left {
            match target {
                SimpleAssignTarget::Ident(ident) => {
                    if ident.id.sym == "Math" && ident.id.ctxt.outer() == self.unresolved_mark {
                        self.mutation.slot = true;
                    }
                    if ident.id.sym == "globalThis" && ident.id.ctxt.outer() == self.unresolved_mark
                    {
                        self.mutation.globalthis = true;
                    }
                }
                SimpleAssignTarget::Member(member) => self.note_member_write(member),
                _ => {}
            }
        }
        expr.visit_children_with(self);
    }

    fn visit_update_expr(&mut self, expr: &UpdateExpr) {
        if self.is_unresolved_global(expr.arg.as_ref(), "Math") {
            self.mutation.slot = true;
        }
        expr.visit_children_with(self);
    }
}

struct DirectEvalScopes {
    top_level: bool,
    functions: Vec<Span>,
}

/// Finds a direct `eval(...)` within a single scope, without descending into
/// nested function-like scopes (each is its own scope). Keys and decorators of
/// class members belong to the *enclosing* scope, so they are still visited.
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
    fn visit_static_block(&mut self, _: &StaticBlock) {}

    fn visit_constructor(&mut self, constructor: &Constructor) {
        constructor.key.visit_with(self);
    }

    fn visit_getter_prop(&mut self, getter: &GetterProp) {
        getter.key.visit_with(self);
    }

    fn visit_setter_prop(&mut self, setter: &SetterProp) {
        setter.key.visit_with(self);
    }

    fn visit_class_prop(&mut self, prop: &ClassProp) {
        prop.key.visit_with(self);
        prop.decorators.visit_with(self);
    }

    fn visit_private_prop(&mut self, prop: &PrivateProp) {
        prop.decorators.visit_with(self);
    }

    fn visit_auto_accessor(&mut self, accessor: &AutoAccessor) {
        accessor.key.visit_with(self);
        accessor.decorators.visit_with(self);
    }

    fn visit_prop_name(&mut self, prop: &PropName) {
        if let PropName::Computed(computed) = prop {
            computed.expr.visit_with(self);
        }
    }
}

struct DirectEvalScopeCollector {
    functions: Vec<Span>,
}

impl DirectEvalScopeCollector {
    fn record_scope(&mut self, span: Span, body: impl FnOnce(&mut DirectEvalFinder)) {
        let mut finder = DirectEvalFinder::default();
        body(&mut finder);
        if finder.found {
            self.functions.push(span);
        }
    }
}

impl Visit for DirectEvalScopeCollector {
    fn visit_function(&mut self, function: &Function) {
        self.record_scope(function.span, |finder| {
            function.params.visit_with(finder);
            function.body.visit_with(finder);
        });
        function.visit_children_with(self);
    }

    fn visit_arrow_expr(&mut self, arrow: &ArrowExpr) {
        self.record_scope(arrow.span, |finder| {
            arrow.params.visit_with(finder);
            arrow.body.visit_with(finder);
        });
        arrow.visit_children_with(self);
    }

    fn visit_constructor(&mut self, constructor: &Constructor) {
        self.record_scope(constructor.span, |finder| {
            constructor.params.visit_with(finder);
            if let Some(body) = &constructor.body {
                body.visit_with(finder);
            }
        });
        constructor.visit_children_with(self);
    }

    fn visit_getter_prop(&mut self, getter: &GetterProp) {
        self.record_scope(getter.function.span, |finder| {
            getter.function.body.visit_with(finder);
        });
        getter.visit_children_with(self);
    }

    fn visit_setter_prop(&mut self, setter: &SetterProp) {
        self.record_scope(setter.function.span, |finder| {
            setter.function.body.visit_with(finder);
        });
        setter.visit_children_with(self);
    }

    fn visit_class_prop(&mut self, prop: &ClassProp) {
        if let Some(value) = &prop.value {
            self.record_scope(value.span(), |finder| value.visit_with(finder));
        }
        prop.visit_children_with(self);
    }

    fn visit_private_prop(&mut self, prop: &PrivateProp) {
        if let Some(value) = &prop.value {
            self.record_scope(value.span(), |finder| value.visit_with(finder));
        }
        prop.visit_children_with(self);
    }

    fn visit_auto_accessor(&mut self, accessor: &AutoAccessor) {
        if let Some(value) = &accessor.value {
            self.record_scope(value.span(), |finder| value.visit_with(finder));
        }
        accessor.visit_children_with(self);
    }

    fn visit_static_block(&mut self, block: &StaticBlock) {
        self.record_scope(block.span, |finder| {
            block.body.stmts.visit_with(finder);
        });
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
