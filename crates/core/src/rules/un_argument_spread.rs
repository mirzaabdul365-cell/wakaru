use std::collections::HashSet;

use swc_core::common::{Mark, Span, Spanned, SyntaxContext, DUMMY_SP};
use swc_core::ecma::ast::{
    AssignOp, AssignTarget, AssignTargetPat, AutoAccessor, CallExpr, Callee, ClassProp,
    Constructor, Expr, ExprOrSpread, ExprStmt, ForHead, GetterProp, Ident, ImportDecl,
    ImportSpecifier, Lit, MemberExpr, MemberProp, Module, NewExpr, ObjectPatProp, OptChainBase,
    Pat, PrivateProp, PropName, SetterProp, SimpleAssignTarget, StaticBlock, Stmt, UnaryExpr,
    UnaryOp, UpdateExpr, VarDeclKind,
};
use swc_core::ecma::visit::{Visit, VisitMut, VisitMutWith, VisitWith};

use super::decl_utils::{
    can_remove_prior_uninitialized_decls, ident_is_used_in_stmts_excluding_bindings,
    remove_prior_uninitialized_decls, same_ident, BindingId, UninitializedDeclKind,
};
use super::eval_utils::is_direct_eval_call;
use super::expr_utils::{
    exprs_structurally_equal, is_unresolved_ident, is_unresolved_undefined, strip_transparent_types,
};
use super::RewriteLevel;

use crate::utils::paren::{strip_parens, strip_parens_owned};

pub struct UnArgumentSpread {
    unresolved_mark: Mark,
    level: RewriteLevel,
    stable_bindings: HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: Vec<Span>,
}

impl UnArgumentSpread {
    pub fn new(unresolved_mark: Mark, level: RewriteLevel) -> Self {
        Self {
            unresolved_mark,
            level,
            stable_bindings: HashSet::new(),
            with_depth: 0,
            top_level_direct_eval: false,
            direct_eval_scopes: Vec::new(),
        }
    }
}

impl Default for UnArgumentSpread {
    fn default() -> Self {
        Self::new(Mark::new(), RewriteLevel::Standard)
    }
}

impl VisitMut for UnArgumentSpread {
    fn visit_mut_module(&mut self, module: &mut Module) {
        self.stable_bindings = collect_stable_bindings(module);
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

    fn visit_mut_stmts(&mut self, stmts: &mut Vec<Stmt>) {
        stmts.visit_mut_children_with(self);

        if self.level < RewriteLevel::Standard {
            return;
        }

        let mut old = std::mem::take(stmts);
        let mut index = 0;
        while index < old.len() {
            if index + 1 < old.len() {
                if let Some(rewrite) = try_convert_split_memoized_apply(
                    &old[index],
                    &old[index + 1],
                    &old[index + 2..],
                ) {
                    if can_remove_prior_uninitialized_decls(
                        stmts,
                        &rewrite.removable_bindings,
                        UninitializedDeclKind::Any,
                    ) {
                        let end = stmts.len();
                        remove_prior_uninitialized_decls(
                            stmts,
                            end,
                            &rewrite.removable_bindings,
                            UninitializedDeclKind::Any,
                        );
                        stmts.push(rewrite.stmt);
                        index += 2;
                        continue;
                    }
                }
            }

            stmts.push(std::mem::replace(
                &mut old[index],
                Stmt::Empty(swc_core::ecma::ast::EmptyStmt { span: DUMMY_SP }),
            ));
            index += 1;
        }
    }

    fn visit_mut_expr(&mut self, expr: &mut Expr) {
        expr.visit_mut_children_with(self);

        if self.level < RewriteLevel::Standard {
            return;
        }

        let taken = match expr {
            Expr::Call(_) => {
                let placeholder = Expr::Lit(Lit::Num(swc_core::ecma::ast::Number {
                    span: DUMMY_SP,
                    value: 0.0,
                    raw: None,
                }));
                std::mem::replace(expr, placeholder)
            }
            _ => return,
        };

        let Expr::Call(call) = taken else {
            *expr = taken;
            return;
        };

        match try_convert_apply(
            call,
            self.unresolved_mark,
            &self.stable_bindings,
            self.with_depth,
            self.top_level_direct_eval,
            &self.direct_eval_scopes,
        ) {
            Ok(new_expr) => *expr = new_expr,
            Err(original_call) => *expr = Expr::Call(original_call),
        }
    }
}

fn try_convert_apply(
    call: CallExpr,
    unresolved_mark: Mark,
    stable_bindings: &HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: &[Span],
) -> Result<Expr, CallExpr> {
    // callee must be a member expression ending in `.apply`
    let callee_member = match &call.callee {
        Callee::Expr(e) => match e.as_ref() {
            Expr::Member(m) => m,
            _ => return Err(call),
        },
        _ => return Err(call),
    };

    let is_reflect_apply = matches!(
        callee_member.obj.as_ref(),
        Expr::Ident(id) if id.sym.as_ref() == "Reflect"
    ) && matches!(&callee_member.prop, MemberProp::Ident(id) if id.sym.as_ref() == "apply");

    if is_reflect_apply && call.args.len() == 3 {
        if !matches!(
            callee_member.obj.as_ref(),
            Expr::Ident(id) if is_unresolved_ident(id, "Reflect", unresolved_mark)
        ) {
            return Err(call);
        }
        if let Some(new_expr) = try_convert_reflect_apply(
            &call,
            callee_member,
            unresolved_mark,
            stable_bindings,
            with_depth,
            top_level_direct_eval,
            direct_eval_scopes,
        ) {
            return Ok(new_expr);
        }
        return Err(call);
    }

    let is_reflect_construct = matches!(
        callee_member.obj.as_ref(),
        Expr::Ident(id) if id.sym.as_ref() == "Reflect"
    ) && matches!(&callee_member.prop, MemberProp::Ident(id) if id.sym.as_ref() == "construct");

    if is_reflect_construct && (call.args.len() == 2 || call.args.len() == 3) {
        if !matches!(
            callee_member.obj.as_ref(),
            Expr::Ident(id) if is_unresolved_ident(id, "Reflect", unresolved_mark)
        ) {
            return Err(call);
        }
        if let Some(new_expr) = try_convert_reflect_construct(
            &call,
            callee_member,
            unresolved_mark,
            stable_bindings,
            with_depth,
            top_level_direct_eval,
            direct_eval_scopes,
        ) {
            return Ok(new_expr);
        }
        return Err(call);
    }

    // Check that the property is `apply`
    match &callee_member.prop {
        MemberProp::Ident(ident_name) if ident_name.sym.as_ref() == "apply" => {}
        _ => return Err(call),
    }

    // We need exactly 2 arguments
    if call.args.len() != 2 {
        return Err(call);
    }

    // Check for spread on either arg – we don't handle those
    if call.args[0].spread.is_some() || call.args[1].spread.is_some() {
        return Err(call);
    }

    let first_arg = call.args[0].expr.as_ref();
    let callee_obj = callee_member.obj.as_ref();

    // Pattern 1: fn.apply(null/undefined, arg2) → fn(...arg2)
    // Only applies when the callee object is NOT itself a member expression
    // (i.e., the callee is just `fn`, not `obj.fn`)
    // Actually per the JS spec, for plain fn.apply(null/undefined) we convert regardless.
    // But if it's obj.fn.apply(obj, ...) we match pattern 2 instead.
    // Determine which pattern applies:

    // Pattern 2: obj.fn.apply(obj, arg2) → obj.fn(...arg2)
    // The callee's object is a member expression AND first arg equals the outer object.
    // e.g. callee = obj.fn.apply, callee_obj = obj.fn (Member), first_arg should = obj
    if let Expr::Member(callee_member_obj) = callee_obj {
        // The non-memoized same-receiver form accepts only an identifier or
        // `this` receiver. A member-chain receiver (`root.child.method.apply(
        // root.child, args)`) is read twice by the input and once by the
        // output, so a getter's evaluation count would change. Babel emits
        // the bare form only for plain identifiers and `this`; it memoizes
        // member receivers, which the memoized paths below handle.
        if matches!(first_arg, Expr::Ident(_) | Expr::This(_))
            && exprs_structurally_equal(first_arg, &callee_member_obj.obj)
        {
            return Ok(make_spread_call(call));
        }
        if let Some(receiver) = memoized_receiver_source(&callee_member_obj.obj, first_arg) {
            return Ok(make_spread_call_with_member_receiver(call, receiver));
        }
        // obj.fn.apply(null/undefined, ...) — Babel spread artifact for standalone
        // function calls on module namespaces (e.g. `r.applyMiddleware.apply(void 0, d)`).
        // Not converted here because it changes `this` from undefined to obj.
        // The proper fix is namespace import decomposition (r.fn → fn), after which
        // Pattern 1 (simple ident) handles it.
        return Err(call);
    }

    // Pattern 1: callee obj is not a member expression, first arg must be null/undefined
    if matches!(first_arg, Expr::Lit(Lit::Null(_)))
        || is_unresolved_undefined(first_arg, unresolved_mark)
    {
        return Ok(make_spread_call(call));
    }

    Err(call)
}

fn try_convert_reflect_apply(
    call: &CallExpr,
    callee_member: &MemberExpr,
    unresolved_mark: Mark,
    stable_bindings: &HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: &[Span],
) -> Option<Expr> {
    if with_depth > 0
        || top_level_direct_eval
        || direct_eval_scopes
            .iter()
            .any(|scope| scope.lo <= call.span.lo && call.span.hi <= scope.hi)
    {
        return None;
    }
    if !matches!(
        callee_member.obj.as_ref(),
        Expr::Ident(id) if is_unresolved_ident(id, "Reflect", unresolved_mark)
    ) || !matches!(&callee_member.prop, MemberProp::Ident(id) if id.sym.as_ref() == "apply")
    {
        return None;
    }
    if call.args.len() != 3 || call.args.iter().any(|arg| arg.spread.is_some()) {
        return None;
    }

    let target_expr = call.args[0].expr.clone();
    let target = strip_transparent_types(target_expr.as_ref());
    let this_arg = strip_transparent_types(call.args[1].expr.as_ref());
    let arguments = Box::new(strip_parens_owned((*call.args[2].expr).clone()));
    let normalized_arguments = strip_transparent_types(arguments.as_ref());

    if matches!(target, Expr::Ident(id) if id.sym.as_ref() == "eval") {
        return None;
    }

    let output_arguments = if matches!(normalized_arguments, Expr::Array(_)) {
        Box::new(normalized_arguments.clone())
    } else {
        arguments
    };

    match target_receiver(target) {
        Some(receiver) => {
            if !exprs_structurally_equal(this_arg, receiver)
                || !receiver_is_stable(receiver, stable_bindings)
            {
                return None;
            }
        }
        None if is_receiver_bearing_target(target) => {
            if !matches!(target, Expr::SuperProp(_)) || !matches!(this_arg, Expr::This(_)) {
                return None;
            }
        }
        None => {
            if !is_reflect_nullish(this_arg, unresolved_mark) {
                return None;
            }
        }
    }

    Some(make_direct_spread_call(*target_expr, output_arguments))
}

/// Recover `Reflect.construct(Target, argumentsList[, newTarget])` into a
/// `new Target(...argumentsList)` expression.
///
/// A `new Target(...)` expression forces `new.target === Target`, so the
/// three-argument form is only sound when the supplied `newTarget` is provably
/// the same value as `Target`. Because a `new` expression evaluates its callee
/// exactly once, a `newTarget` that re-reads a property (any member target)
/// would collapse two reads into one and could observe a different value; we
/// therefore accept the three-argument form only for a standalone identifier
/// bound to a lexically stable binding, whose `newTarget` is the structurally
/// identical identifier. Reads of such a binding during consecutive argument
/// evaluation are side-effect-free and yield the same value.
fn try_convert_reflect_construct(
    call: &CallExpr,
    callee_member: &MemberExpr,
    unresolved_mark: Mark,
    stable_bindings: &HashSet<BindingId>,
    with_depth: usize,
    top_level_direct_eval: bool,
    direct_eval_scopes: &[Span],
) -> Option<Expr> {
    if with_depth > 0
        || top_level_direct_eval
        || direct_eval_scopes
            .iter()
            .any(|scope| scope.lo <= call.span.lo && call.span.hi <= scope.hi)
    {
        return None;
    }
    if !matches!(
        callee_member.obj.as_ref(),
        Expr::Ident(id) if is_unresolved_ident(id, "Reflect", unresolved_mark)
    ) || !matches!(&callee_member.prop, MemberProp::Ident(id) if id.sym.as_ref() == "construct")
    {
        return None;
    }
    let arg_count = call.args.len();
    if !(arg_count == 2 || arg_count == 3) || call.args.iter().any(|arg| arg.spread.is_some()) {
        return None;
    }

    let target_expr = call.args[0].expr.clone();
    let target = strip_transparent_types(target_expr.as_ref());

    if matches!(target, Expr::Ident(id) if id.sym.as_ref() == "eval") {
        return None;
    }

    if arg_count == 3 {
        // newTarget correctness gate: standalone stable identifier only.
        let Expr::Ident(target_ident) = target else {
            return None;
        };
        if !stable_bindings.contains(&(target_ident.sym.clone(), target_ident.ctxt)) {
            return None;
        }
        let new_target = strip_transparent_types(call.args[2].expr.as_ref());
        if !exprs_structurally_equal(target, new_target) {
            return None;
        }
    } else {
        // Two-argument form: the target is evaluated exactly once in both the
        // input and the recovered `new` expression. Standalone identifiers are
        // always eligible; member targets require a stable receiver, matching
        // the receiver rules used by the `Reflect.apply` recovery.
        match target {
            Expr::Ident(_) => {}
            Expr::Member(member) => {
                let receiver = strip_parens(member.obj.as_ref());
                if !receiver_is_stable(receiver, stable_bindings)
                    || !matches!(&member.prop, MemberProp::Ident(_) | MemberProp::Computed(_))
                {
                    return None;
                }
            }
            _ => return None,
        }
    }

    let arguments = Box::new(strip_parens_owned((*call.args[1].expr).clone()));
    let normalized_arguments = strip_transparent_types(arguments.as_ref());

    let output_arguments = if matches!(normalized_arguments, Expr::Array(_)) {
        Box::new(normalized_arguments.clone())
    } else {
        arguments
    };

    Some(make_new_spread_call(*target_expr, output_arguments))
}

fn make_new_spread_call(callee: Expr, arguments: Box<Expr>) -> Expr {
    Expr::New(NewExpr {
        span: DUMMY_SP,
        ctxt: SyntaxContext::empty(),
        callee: Box::new(callee),
        args: Some(vec![ExprOrSpread {
            spread: Some(DUMMY_SP),
            expr: arguments,
        }]),
        type_args: None,
    })
}

fn is_reflect_nullish(expr: &Expr, unresolved_mark: Mark) -> bool {
    is_unresolved_undefined(expr, unresolved_mark)
        || matches!(expr, Expr::Lit(Lit::Null(_)))
        || matches!(
            expr,
            Expr::Unary(UnaryExpr {
                op: UnaryOp::Void,
                arg,
                ..
            }) if matches!(strip_parens(arg), Expr::Lit(Lit::Num(number)) if number.value == 0.0)
        )
}

fn target_receiver(target: &Expr) -> Option<&Expr> {
    match target {
        Expr::Member(member) => Some(strip_parens(member.obj.as_ref())),
        Expr::OptChain(chain) => match chain.base.as_ref() {
            OptChainBase::Member(member) => Some(strip_parens(member.obj.as_ref())),
            OptChainBase::Call(_) => None,
        },
        _ => None,
    }
}

fn is_receiver_bearing_target(target: &Expr) -> bool {
    matches!(target, Expr::Member(_) | Expr::SuperProp(_))
        || matches!(target, Expr::OptChain(chain) if matches!(
            chain.base.as_ref(),
            OptChainBase::Member(_)
        ))
}

fn receiver_is_stable(expr: &Expr, stable_bindings: &HashSet<BindingId>) -> bool {
    match expr {
        Expr::This(_) => true,
        Expr::Ident(id) => stable_bindings.contains(&(id.sym.clone(), id.ctxt)),
        _ => false,
    }
}

struct DirectEvalScopes {
    top_level: bool,
    functions: Vec<Span>,
}

#[derive(Default)]
struct DirectEvalFinder {
    found: bool,
}

impl Visit for DirectEvalFinder {
    fn visit_call_expr(&mut self, call: &CallExpr) {
        if is_direct_eval_call(call) {
            self.found = true;
            return;
        }
        call.visit_children_with(self);
    }

    fn visit_function(&mut self, _: &swc_core::ecma::ast::Function) {}

    fn visit_arrow_expr(&mut self, _: &swc_core::ecma::ast::ArrowExpr) {}

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

    fn visit_pat(&mut self, pat: &Pat) {
        match pat {
            Pat::Ident(_) | Pat::Invalid(_) => {}
            Pat::Array(array) => {
                for elem in array.elems.iter().flatten() {
                    elem.visit_with(self);
                }
            }
            Pat::Object(object) => {
                for prop in &object.props {
                    match prop {
                        ObjectPatProp::KeyValue(prop) => {
                            prop.key.visit_with(self);
                            prop.value.visit_with(self);
                        }
                        ObjectPatProp::Assign(prop) => prop.value.visit_with(self),
                        ObjectPatProp::Rest(prop) => prop.arg.visit_with(self),
                    }
                }
            }
            Pat::Assign(assign) => {
                assign.left.visit_with(self);
                assign.right.visit_with(self);
            }
            Pat::Rest(rest) => rest.arg.visit_with(self),
            Pat::Expr(expr) => expr.visit_with(self),
        }
    }

    fn visit_prop_name(&mut self, prop: &PropName) {
        if let PropName::Computed(prop) = prop {
            prop.expr.visit_with(self);
        }
    }
}

struct DirectEvalScopeCollector {
    functions: Vec<Span>,
}

impl Visit for DirectEvalScopeCollector {
    fn visit_function(&mut self, function: &swc_core::ecma::ast::Function) {
        let mut finder = DirectEvalFinder::default();
        function.params.visit_with(&mut finder);
        function.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(function.span);
        }
        function.visit_children_with(self);
    }

    fn visit_arrow_expr(&mut self, arrow: &swc_core::ecma::ast::ArrowExpr) {
        let mut finder = DirectEvalFinder::default();
        arrow.params.visit_with(&mut finder);
        arrow.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(arrow.span);
        }
        arrow.visit_children_with(self);
    }

    fn visit_static_block(&mut self, block: &StaticBlock) {
        let mut finder = DirectEvalFinder::default();
        block.body.stmts.visit_with(&mut finder);
        if finder.found {
            self.functions.push(block.span);
        }
        block.visit_children_with(self);
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

    fn visit_getter_prop(&mut self, getter: &GetterProp) {
        let mut finder = DirectEvalFinder::default();
        getter.function.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(getter.function.span);
        }
        getter.visit_children_with(self);
    }

    fn visit_setter_prop(&mut self, setter: &SetterProp) {
        let mut finder = DirectEvalFinder::default();
        setter.function.body.visit_with(&mut finder);
        if finder.found {
            self.functions.push(setter.function.span);
        }
        setter.visit_children_with(self);
    }

    fn visit_class_prop(&mut self, prop: &ClassProp) {
        let mut finder = DirectEvalFinder::default();
        if let Some(value) = &prop.value {
            value.visit_with(&mut finder);
            if finder.found {
                self.functions.push(value.span());
            }
        }
        prop.visit_children_with(self);
    }

    fn visit_private_prop(&mut self, prop: &PrivateProp) {
        let mut finder = DirectEvalFinder::default();
        if let Some(value) = &prop.value {
            value.visit_with(&mut finder);
            if finder.found {
                self.functions.push(value.span());
            }
        }
        prop.visit_children_with(self);
    }

    fn visit_auto_accessor(&mut self, accessor: &AutoAccessor) {
        let mut finder = DirectEvalFinder::default();
        if let Some(value) = &accessor.value {
            value.visit_with(&mut finder);
            if finder.found {
                self.functions.push(value.span());
            }
        }
        accessor.visit_children_with(self);
    }
}

fn collect_direct_eval_scopes(module: &Module) -> DirectEvalScopes {
    let mut top_level_finder = DirectEvalFinder::default();
    module.visit_with(&mut top_level_finder);

    let mut collector = DirectEvalScopeCollector {
        functions: Vec::new(),
    };
    module.visit_with(&mut collector);

    DirectEvalScopes {
        top_level: top_level_finder.found,
        functions: collector.functions,
    }
}

fn collect_stable_bindings(module: &Module) -> HashSet<BindingId> {
    let mut collector = StableBindingCollector {
        const_bindings: HashSet::new(),
        writes: HashSet::new(),
    };
    module.visit_with(&mut collector);
    collector
        .const_bindings
        .difference(&collector.writes)
        .cloned()
        .collect()
}

struct StableBindingCollector {
    const_bindings: HashSet<BindingId>,
    writes: HashSet<BindingId>,
}

impl Visit for StableBindingCollector {
    fn visit_import_decl(&mut self, decl: &ImportDecl) {
        for specifier in &decl.specifiers {
            if let ImportSpecifier::Namespace(specifier) = specifier {
                self.const_bindings
                    .insert((specifier.local.sym.clone(), specifier.local.ctxt));
            }
        }
    }

    fn visit_var_decl(&mut self, decl: &swc_core::ecma::ast::VarDecl) {
        if decl.kind == VarDeclKind::Const {
            for item in &decl.decls {
                collect_const_pattern_ids(&item.name, &mut self.const_bindings);
                if let Some(init) = &item.init {
                    init.visit_with(self);
                }
            }
        } else {
            decl.visit_children_with(self);
        }
    }

    fn visit_assign_expr(&mut self, expr: &swc_core::ecma::ast::AssignExpr) {
        collect_assign_target_ids(&expr.left, &mut self.writes);
        expr.visit_children_with(self);
    }

    fn visit_update_expr(&mut self, expr: &UpdateExpr) {
        collect_assignment_expr_ids(expr.arg.as_ref(), &mut self.writes);
        expr.visit_children_with(self);
    }

    fn visit_for_in_stmt(&mut self, stmt: &swc_core::ecma::ast::ForInStmt) {
        collect_for_head_assignment_ids(&stmt.left, &mut self.writes);
        stmt.visit_children_with(self);
    }

    fn visit_for_of_stmt(&mut self, stmt: &swc_core::ecma::ast::ForOfStmt) {
        collect_for_head_assignment_ids(&stmt.left, &mut self.writes);
        stmt.visit_children_with(self);
    }
}

fn collect_const_pattern_ids(pat: &Pat, out: &mut HashSet<BindingId>) {
    match pat {
        Pat::Ident(binding) => {
            out.insert((binding.id.sym.clone(), binding.id.ctxt));
        }
        Pat::Array(array) => {
            for elem in array.elems.iter().flatten() {
                collect_const_pattern_ids(elem, out);
            }
        }
        Pat::Object(object) => {
            for prop in &object.props {
                match prop {
                    ObjectPatProp::KeyValue(prop) => {
                        collect_const_pattern_ids(&prop.value, out);
                    }
                    ObjectPatProp::Assign(prop) => {
                        out.insert((prop.key.sym.clone(), prop.key.ctxt));
                    }
                    ObjectPatProp::Rest(prop) => {
                        collect_const_pattern_ids(&prop.arg, out);
                    }
                }
            }
        }
        Pat::Assign(assign) => collect_const_pattern_ids(&assign.left, out),
        Pat::Rest(rest) => collect_const_pattern_ids(&rest.arg, out),
        Pat::Expr(_) | Pat::Invalid(_) => {}
    }
}

fn collect_assign_target_ids(target: &AssignTarget, out: &mut HashSet<BindingId>) {
    match target {
        AssignTarget::Simple(simple) => collect_simple_assign_target_ids(simple, out),
        AssignTarget::Pat(pat) => collect_assign_target_pat_ids(pat, out),
    }
}

fn collect_simple_assign_target_ids(target: &SimpleAssignTarget, out: &mut HashSet<BindingId>) {
    match target {
        SimpleAssignTarget::Ident(binding) => {
            out.insert((binding.id.sym.clone(), binding.id.ctxt));
        }
        SimpleAssignTarget::Paren(paren) => collect_assignment_expr_ids(&paren.expr, out),
        SimpleAssignTarget::TsAs(expr) => collect_assignment_expr_ids(&expr.expr, out),
        SimpleAssignTarget::TsSatisfies(expr) => collect_assignment_expr_ids(&expr.expr, out),
        SimpleAssignTarget::TsNonNull(expr) => collect_assignment_expr_ids(&expr.expr, out),
        SimpleAssignTarget::TsTypeAssertion(expr) => collect_assignment_expr_ids(&expr.expr, out),
        SimpleAssignTarget::TsInstantiation(expr) => collect_assignment_expr_ids(&expr.expr, out),
        SimpleAssignTarget::Member(_)
        | SimpleAssignTarget::SuperProp(_)
        | SimpleAssignTarget::OptChain(_)
        | SimpleAssignTarget::Invalid(_) => {}
    }
}

fn collect_assignment_expr_ids(expr: &Expr, out: &mut HashSet<BindingId>) {
    match expr {
        Expr::Ident(id) => {
            out.insert((id.sym.clone(), id.ctxt));
        }
        Expr::Paren(paren) => collect_assignment_expr_ids(&paren.expr, out),
        Expr::TsAs(expr) => collect_assignment_expr_ids(&expr.expr, out),
        Expr::TsSatisfies(expr) => collect_assignment_expr_ids(&expr.expr, out),
        Expr::TsNonNull(expr) => collect_assignment_expr_ids(&expr.expr, out),
        Expr::TsTypeAssertion(expr) => collect_assignment_expr_ids(&expr.expr, out),
        Expr::TsInstantiation(expr) => collect_assignment_expr_ids(&expr.expr, out),
        _ => {}
    }
}

fn collect_assign_target_pat_ids(pat: &AssignTargetPat, out: &mut HashSet<BindingId>) {
    match pat {
        AssignTargetPat::Array(array) => {
            for elem in array.elems.iter().flatten() {
                collect_assignment_pat_ids(elem, out);
            }
        }
        AssignTargetPat::Object(object) => {
            for prop in &object.props {
                match prop {
                    ObjectPatProp::KeyValue(prop) => {
                        collect_assignment_pat_ids(&prop.value, out);
                    }
                    ObjectPatProp::Assign(prop) => {
                        out.insert((prop.key.sym.clone(), prop.key.ctxt));
                    }
                    ObjectPatProp::Rest(prop) => {
                        collect_assignment_pat_ids(&prop.arg, out);
                    }
                }
            }
        }
        AssignTargetPat::Invalid(_) => {}
    }
}

fn collect_assignment_pat_ids(pat: &Pat, out: &mut HashSet<BindingId>) {
    match pat {
        Pat::Ident(binding) => {
            out.insert((binding.id.sym.clone(), binding.id.ctxt));
        }
        Pat::Array(array) => {
            for elem in array.elems.iter().flatten() {
                collect_assignment_pat_ids(elem, out);
            }
        }
        Pat::Object(object) => {
            for prop in &object.props {
                match prop {
                    ObjectPatProp::KeyValue(prop) => {
                        collect_assignment_pat_ids(&prop.value, out);
                    }
                    ObjectPatProp::Assign(prop) => {
                        out.insert((prop.key.sym.clone(), prop.key.ctxt));
                    }
                    ObjectPatProp::Rest(prop) => {
                        collect_assignment_pat_ids(&prop.arg, out);
                    }
                }
            }
        }
        Pat::Assign(assign) => collect_assignment_pat_ids(&assign.left, out),
        Pat::Rest(rest) => collect_assignment_pat_ids(&rest.arg, out),
        Pat::Expr(expr) => collect_assignment_expr_ids(expr, out),
        Pat::Invalid(_) => {}
    }
}

fn collect_for_head_assignment_ids(head: &ForHead, out: &mut HashSet<BindingId>) {
    if let ForHead::Pat(pat) = head {
        collect_assignment_pat_ids(pat, out);
    }
}

fn try_convert_split_memoized_apply(
    method_stmt: &Stmt,
    apply_stmt: &Stmt,
    rest: &[Stmt],
) -> Option<SplitMemoizedApplyRewrite> {
    let (method_temp, memoized_member) = memoized_method_assignment(method_stmt)?;
    let apply_call = expr_stmt_call(apply_stmt)?;

    if apply_call.args.len() != 2
        || apply_call.args[0].spread.is_some()
        || apply_call.args[1].spread.is_some()
    {
        return None;
    }

    let apply_member = match &apply_call.callee {
        Callee::Expr(callee) => match callee.as_ref() {
            Expr::Member(member) => member,
            _ => return None,
        },
        _ => return None,
    };
    if !matches!(&apply_member.prop, MemberProp::Ident(prop) if prop.sym.as_ref() == "apply") {
        return None;
    }
    if !matches!(apply_member.obj.as_ref(), Expr::Ident(id) if same_ident(id, &method_temp)) {
        return None;
    }

    let first_arg = apply_call.args[0].expr.as_ref();
    let mut removable_bindings = vec![method_temp.clone()];
    let receiver = if exprs_structurally_equal(first_arg, &memoized_member.obj) {
        memoized_member.obj.clone()
    } else {
        let receiver_temp = ident_expr(first_arg)?;
        removable_bindings.push(receiver_temp.clone());
        memoized_receiver_source(&memoized_member.obj, first_arg)?
    };

    if removable_bindings
        .iter()
        .any(|binding| ident_is_used_in_stmts_excluding_bindings(binding, rest))
    {
        return None;
    }

    let mut args = args_from_apply_arg(apply_call.args[1].expr.clone());
    let callee = Expr::Member(MemberExpr {
        span: memoized_member.span,
        obj: receiver,
        prop: memoized_member.prop.clone(),
    });

    Some(SplitMemoizedApplyRewrite {
        stmt: Stmt::Expr(ExprStmt {
            span: apply_call.span,
            expr: Box::new(Expr::Call(CallExpr {
                span: apply_call.span,
                ctxt: apply_call.ctxt,
                callee: Callee::Expr(Box::new(callee)),
                args: std::mem::take(&mut args),
                type_args: apply_call.type_args.clone(),
            })),
        }),
        removable_bindings,
    })
}

struct SplitMemoizedApplyRewrite {
    stmt: Stmt,
    removable_bindings: Vec<Ident>,
}

fn memoized_method_assignment(stmt: &Stmt) -> Option<(Ident, &MemberExpr)> {
    let Stmt::Expr(expr_stmt) = stmt else {
        return None;
    };
    let Expr::Assign(assign) = expr_stmt.expr.as_ref() else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let AssignTarget::Simple(SimpleAssignTarget::Ident(method_temp)) = &assign.left else {
        return None;
    };
    let Expr::Member(member) = assign.right.as_ref() else {
        return None;
    };
    Some((method_temp.id.clone(), member))
}

fn expr_stmt_call(stmt: &Stmt) -> Option<&CallExpr> {
    let Stmt::Expr(expr_stmt) = stmt else {
        return None;
    };
    let Expr::Call(call) = expr_stmt.expr.as_ref() else {
        return None;
    };
    Some(call)
}

fn ident_expr(expr: &Expr) -> Option<&Ident> {
    match expr {
        Expr::Ident(ident) => Some(ident),
        _ => None,
    }
}

fn args_from_apply_arg(arg: Box<Expr>) -> Vec<ExprOrSpread> {
    match *arg {
        Expr::Array(array) if array.elems.iter().all(Option::is_some) => {
            array.elems.into_iter().flatten().collect()
        }
        expr => vec![ExprOrSpread {
            spread: Some(DUMMY_SP),
            expr: Box::new(expr),
        }],
    }
}

/// Build `fn(...secondArg)` from the original `.apply(thisArg, secondArg)` call.
fn make_spread_call(call: CallExpr) -> Expr {
    // Consume the call
    let CallExpr {
        span,
        ctxt,
        callee,
        mut args,
        type_args,
    } = call;

    // callee is `fn.apply` – we want just `fn`
    let Callee::Expr(callee_box) = callee else {
        unreachable!()
    };
    let Expr::Member(member) = *callee_box else {
        unreachable!()
    };
    let fn_expr = member.obj;

    // second arg becomes the spread argument
    let second_arg = args.remove(1).expr;

    make_direct_spread_call_with_parts(span, ctxt, fn_expr, second_arg, type_args)
}

fn make_direct_spread_call(callee: Expr, arguments: Box<Expr>) -> Expr {
    make_direct_spread_call_with_parts(
        DUMMY_SP,
        swc_core::common::SyntaxContext::empty(),
        Box::new(callee),
        arguments,
        None,
    )
}

fn make_direct_spread_call_with_parts(
    span: swc_core::common::Span,
    ctxt: swc_core::common::SyntaxContext,
    callee: Box<Expr>,
    arguments: Box<Expr>,
    type_args: Option<Box<swc_core::ecma::ast::TsTypeParamInstantiation>>,
) -> Expr {
    Expr::Call(CallExpr {
        span,
        ctxt,
        callee: Callee::Expr(callee),
        args: vec![ExprOrSpread {
            spread: Some(DUMMY_SP),
            expr: arguments,
        }],
        type_args,
    })
}

fn memoized_receiver_source(receiver_expr: &Expr, first_arg: &Expr) -> Option<Box<Expr>> {
    let receiver_expr = strip_parens(receiver_expr);
    let Expr::Assign(assign) = receiver_expr else {
        return None;
    };
    if assign.op != AssignOp::Assign {
        return None;
    }
    let AssignTarget::Simple(SimpleAssignTarget::Ident(target)) = &assign.left else {
        return None;
    };
    if !matches!(first_arg, Expr::Ident(id) if id.sym == target.id.sym && id.ctxt == target.id.ctxt)
    {
        return None;
    }
    Some(assign.right.clone())
}

fn make_spread_call_with_member_receiver(mut call: CallExpr, receiver: Box<Expr>) -> Expr {
    if let Callee::Expr(callee) = &mut call.callee {
        if let Expr::Member(apply_member) = callee.as_mut() {
            if let Expr::Member(fn_member) = apply_member.obj.as_mut() {
                fn_member.obj = receiver;
            }
        }
    }
    make_spread_call(call)
}
