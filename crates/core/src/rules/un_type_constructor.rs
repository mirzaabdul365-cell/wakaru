use swc_core::common::util::take::Take;
use swc_core::common::{Span, Spanned, DUMMY_SP};
use swc_core::ecma::ast::{
    ArrayLit, BinExpr, BinaryOp, CallExpr, CondExpr, Expr, ExprOrSpread, Ident, Lit, Number, Str,
    Tpl, UnaryExpr, UnaryOp,
};
use swc_core::ecma::utils::ExprFactory;
use swc_core::ecma::visit::{VisitMut, VisitMutWith};

use super::RewriteLevel;

pub struct UnTypeConstructor {
    level: RewriteLevel,
}

impl UnTypeConstructor {
    pub fn new(level: RewriteLevel) -> Self {
        Self { level }
    }
}

impl Default for UnTypeConstructor {
    fn default() -> Self {
        Self::new(RewriteLevel::Standard)
    }
}

impl VisitMut for UnTypeConstructor {
    fn visit_mut_expr(&mut self, expr: &mut Expr) {
        if self.level < RewriteLevel::Aggressive {
            return;
        }
        expr.visit_mut_children_with(self);

        let original_span = expr.span();
        match expr {
            // +x → Number(x) — only when x is an Ident
            Expr::Unary(UnaryExpr {
                op: UnaryOp::Plus,
                arg,
                ..
            }) if matches!(**arg, Expr::Ident(_)) => {
                let arg = std::mem::replace(
                    arg,
                    Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: 0.0,
                        raw: None,
                    }))),
                );
                *expr = make_call("Number", arg, original_span);
            }

            // x + "" → String(x)  OR  "str" + "" → "str"
            Expr::Bin(BinExpr {
                op: BinaryOp::Add,
                left,
                right,
                ..
            }) if is_empty_string(right) => {
                if is_string_lit(left) {
                    let left = std::mem::replace(
                        left,
                        Box::new(Expr::Lit(Lit::Num(Number {
                            span: DUMMY_SP,
                            value: 0.0,
                            raw: None,
                        }))),
                    );
                    *expr = *left;
                } else {
                    let left = std::mem::replace(
                        left,
                        Box::new(Expr::Lit(Lit::Num(Number {
                            span: DUMMY_SP,
                            value: 0.0,
                            raw: None,
                        }))),
                    );
                    *expr = make_call("String", left, original_span);
                }
            }

            // [,,,] → Array(n) — all-holes array with n > 0
            Expr::Array(ArrayLit { elems, .. }) if is_all_holes(elems) && !elems.is_empty() => {
                let n = elems.len();
                *expr = make_call(
                    "Array",
                    Box::new(Expr::Lit(Lit::Num(Number {
                        span: DUMMY_SP,
                        value: n as f64,
                        raw: None,
                    }))),
                    original_span,
                );
            }

            // "" + x → String(x) — the empty string is on the left (mirror of the
            // x + "" case above). Only when the right side is not itself a string
            // literal (string + string is plain concatenation, not a coercion).
            Expr::Bin(BinExpr {
                op: BinaryOp::Add,
                left,
                right,
                ..
            }) if is_empty_string(left) && !is_string_lit(right) => {
                let Expr::Bin(bin) = expr.take() else {
                    unreachable!()
                };
                *expr = make_call("String", bin.right, original_span);
            }

            // `${x}` → String(x) — a template literal that is a single
            // interpolation with no surrounding text uses ToString on `x`.
            Expr::Tpl(tpl) if is_lone_interpolation(tpl) => {
                let Expr::Tpl(mut tpl) = expr.take() else {
                    unreachable!()
                };
                let arg = tpl.exprs.pop().unwrap();
                *expr = make_call("String", arg, original_span);
            }

            // !!x → Boolean(x)
            Expr::Unary(UnaryExpr {
                op: UnaryOp::Bang,
                arg,
                ..
            }) if matches!(
                arg.as_ref(),
                Expr::Unary(UnaryExpr {
                    op: UnaryOp::Bang,
                    ..
                })
            ) =>
            {
                let Expr::Unary(outer) = expr.take() else {
                    unreachable!()
                };
                let Expr::Unary(inner) = *outer.arg else {
                    unreachable!()
                };
                *expr = make_call("Boolean", inner.arg, original_span);
            }

            // x ? true : false → Boolean(x)
            Expr::Cond(CondExpr { cons, alt, .. })
                if is_bool_lit(cons, true) && is_bool_lit(alt, false) =>
            {
                let Expr::Cond(cond) = expr.take() else {
                    unreachable!()
                };
                *expr = make_call("Boolean", cond.test, original_span);
            }

            // x * 1 → Number(x) — identifier operand only, matching the +x case.
            Expr::Bin(BinExpr {
                op: BinaryOp::Mul,
                left,
                right,
                ..
            }) if matches!(left.as_ref(), Expr::Ident(_)) && is_number_lit(right, 1.0) => {
                let Expr::Bin(bin) = expr.take() else {
                    unreachable!()
                };
                *expr = make_call("Number", bin.left, original_span);
            }

            // x - 0 → Number(x) — identifier operand only.
            Expr::Bin(BinExpr {
                op: BinaryOp::Sub,
                left,
                right,
                ..
            }) if matches!(left.as_ref(), Expr::Ident(_)) && is_number_lit(right, 0.0) => {
                let Expr::Bin(bin) = expr.take() else {
                    unreachable!()
                };
                *expr = make_call("Number", bin.left, original_span);
            }

            _ => {}
        }
    }
}

fn is_bool_lit(expr: &Expr, value: bool) -> bool {
    matches!(expr, Expr::Lit(Lit::Bool(b)) if b.value == value)
}

fn is_number_lit(expr: &Expr, value: f64) -> bool {
    matches!(expr, Expr::Lit(Lit::Num(n)) if n.value == value)
}

/// `${x}`: exactly one interpolation and no literal text around it.
fn is_lone_interpolation(tpl: &Tpl) -> bool {
    tpl.exprs.len() == 1 && tpl.quasis.iter().all(|q| q.raw.is_empty())
}

fn make_call(name: &str, arg: Box<Expr>, span: Span) -> Expr {
    Expr::Call(CallExpr {
        span,
        ctxt: Default::default(),
        callee: Expr::Ident(Ident::new_no_ctxt(name.into(), DUMMY_SP)).as_callee(),
        args: vec![arg.as_arg()],
        type_args: None,
    })
}

fn is_empty_string(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(Lit::Str(Str { value, .. })) if value.is_empty())
}

fn is_string_lit(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(Lit::Str(_)))
}

fn is_all_holes(elems: &[Option<ExprOrSpread>]) -> bool {
    elems.iter().all(|e| e.is_none())
}
