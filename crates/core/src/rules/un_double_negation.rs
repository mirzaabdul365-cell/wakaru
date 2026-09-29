use swc_core::common::util::take::Take;
use swc_core::ecma::ast::{
    BinExpr, BinaryOp, CondExpr, DoWhileStmt, Expr, ForStmt, IfStmt, UnaryExpr, UnaryOp, WhileStmt,
};
use swc_core::ecma::visit::{VisitMut, VisitMutWith};

/// Removes redundant double negation (`!!x` -> `x`) in positions where only the
/// truthiness of the value is observed.
///
/// The safe positions are the boolean-coerced tests of `if`/`while`/`do-while`/
/// `for` statements and the test of a conditional expression. Boolean context
/// propagates from those roots through `&&`, `||`, the operand of `!`, and the
/// branches of a nested conditional, because in every one of those positions
/// only the operand's truthiness affects the enclosing coerced result. It never
/// enters a value position: `const b = !!x`, `a && !!x` outside a boolean test,
/// or a conditional branch whose result is used as a value all keep `!!`,
/// because there the boolean produced by `!!` is semantically meaningful.
pub struct UnDoubleNegation;

impl VisitMut for UnDoubleNegation {
    fn visit_mut_if_stmt(&mut self, stmt: &mut IfStmt) {
        stmt.visit_mut_children_with(self);
        strip_in_boolean_context(&mut stmt.test);
    }

    fn visit_mut_while_stmt(&mut self, stmt: &mut WhileStmt) {
        stmt.visit_mut_children_with(self);
        strip_in_boolean_context(&mut stmt.test);
    }

    fn visit_mut_do_while_stmt(&mut self, stmt: &mut DoWhileStmt) {
        stmt.visit_mut_children_with(self);
        strip_in_boolean_context(&mut stmt.test);
    }

    fn visit_mut_for_stmt(&mut self, stmt: &mut ForStmt) {
        stmt.visit_mut_children_with(self);
        if let Some(test) = &mut stmt.test {
            strip_in_boolean_context(test);
        }
    }

    fn visit_mut_cond_expr(&mut self, expr: &mut CondExpr) {
        expr.visit_mut_children_with(self);
        // The test of a conditional is always boolean-coerced. The branches are
        // only in boolean context when the whole conditional is, which is
        // handled by propagation from a boolean root; do not touch them here.
        strip_in_boolean_context(&mut expr.test);
    }

    fn visit_mut_expr(&mut self, expr: &mut Expr) {
        expr.visit_mut_children_with(self);
        // The operand of `!` is boolean-coerced in every position, so `!!` inside
        // it is redundant regardless of where the `!` itself appears.
        if let Expr::Unary(UnaryExpr {
            op: UnaryOp::Bang,
            arg,
            ..
        }) = expr
        {
            strip_in_boolean_context(arg);
        }
    }
}

/// Strip redundant `!!` at `expr`, which is known to be in boolean context, and
/// propagate that context into the sub-expressions that inherit it.
fn strip_in_boolean_context(expr: &mut Expr) {
    // Collapse one or more leading double negations (`!!x`, `!!!!x`, ...).
    loop {
        let collapsed = match expr {
            Expr::Unary(UnaryExpr {
                op: UnaryOp::Bang,
                arg,
                ..
            }) => match &mut **arg {
                Expr::Unary(UnaryExpr {
                    op: UnaryOp::Bang,
                    arg: inner,
                    ..
                }) => Some(inner.take()),
                _ => None,
            },
            _ => None,
        };
        match collapsed {
            Some(inner) => *expr = *inner,
            None => break,
        }
    }

    match expr {
        Expr::Paren(paren) => strip_in_boolean_context(&mut paren.expr),
        // `!x` coerces `x` to boolean, so its operand stays in boolean context.
        Expr::Unary(UnaryExpr {
            op: UnaryOp::Bang,
            arg,
            ..
        }) => strip_in_boolean_context(arg),
        // The coerced result of `&&` / `||` depends only on the truthiness of
        // each operand, so both inherit boolean context.
        Expr::Bin(BinExpr {
            op: BinaryOp::LogicalAnd | BinaryOp::LogicalOr,
            left,
            right,
            ..
        }) => {
            strip_in_boolean_context(left);
            strip_in_boolean_context(right);
        }
        // Reached only for a conditional already in boolean context (never the
        // top-level `visit_mut_cond_expr` path): its branches inherit it too.
        Expr::Cond(CondExpr {
            test, cons, alt, ..
        }) => {
            strip_in_boolean_context(test);
            strip_in_boolean_context(cons);
            strip_in_boolean_context(alt);
        }
        // A comma sequence yields its last operand; only that operand's
        // truthiness reaches the coerced result. Earlier operands are evaluated
        // only for their side effects and keep their `!!`.
        Expr::Seq(seq) => {
            if let Some(last) = seq.exprs.last_mut() {
                strip_in_boolean_context(last);
            }
        }
        _ => {}
    }
}
