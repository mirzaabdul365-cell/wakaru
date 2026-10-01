mod common;

use common::{assert_eq_normalized, render_rule};
use wakaru_core::{rules::UnTypeConstructor, RewriteLevel};

fn apply(input: &str) -> String {
    render_rule(input, |_| UnTypeConstructor::new(RewriteLevel::Aggressive))
}

fn apply_standard(input: &str) -> String {
    render_rule(input, |_| UnTypeConstructor::new(RewriteLevel::Standard))
}

// --- "" + x  →  String(x) ----------------------------------------------------

#[test]
fn leading_empty_string_concat_becomes_string_call() {
    assert_eq_normalized(&apply("const a = \"\" + name;"), "const a = String(name);");
}

#[test]
fn non_empty_leading_string_concat_is_unchanged() {
    let input = "const a = \"x\" + label;";
    assert_eq_normalized(&apply(input), input);
}

// --- `${x}`  →  String(x) ----------------------------------------------------

#[test]
fn lone_template_interpolation_becomes_string_call() {
    assert_eq_normalized(
        &apply("const out = `${value}`;"),
        "const out = String(value);",
    );
}

#[test]
fn template_with_surrounding_text_is_unchanged() {
    let input = "const out = `n${value}`;";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn template_with_two_interpolations_is_unchanged() {
    let input = "const out = `${value}${rest}`;";
    assert_eq_normalized(&apply(input), input);
}

// --- !!x  →  Boolean(x) ------------------------------------------------------

#[test]
fn double_negation_becomes_boolean_call() {
    assert_eq_normalized(&apply("const ok = !!flag;"), "const ok = Boolean(flag);");
}

#[test]
fn single_negation_is_unchanged() {
    let input = "const ok = !flag;";
    assert_eq_normalized(&apply(input), input);
}

// --- ternary ------------------------------------------------------------------
// A ternary whose branches are not the boolean pair is never a coercion, so it
// is left alone regardless of branch order.

#[test]
fn numeric_ternary_is_unchanged() {
    let input = "const ok = cond ? 1 : 0;";
    assert_eq_normalized(&apply(input), input);
}

// --- x * 1  →  Number(x) -----------------------------------------------------

#[test]
fn multiply_by_one_becomes_number_call() {
    assert_eq_normalized(
        &apply("const total = count * 1;"),
        "const total = Number(count);",
    );
}

#[test]
fn multiply_by_other_is_unchanged() {
    let input = "const total = count * 2;";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn multiply_by_one_with_non_ident_operand_is_unchanged() {
    let input = "const total = getValue() * 1;";
    assert_eq_normalized(&apply(input), input);
}

// --- x - 0  →  Number(x) -----------------------------------------------------

#[test]
fn subtract_zero_becomes_number_call() {
    assert_eq_normalized(
        &apply("const amount = price - 0;"),
        "const amount = Number(price);",
    );
}

#[test]
fn subtract_other_is_unchanged() {
    let input = "const amount = price - 1;";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn subtract_zero_with_non_ident_operand_is_unchanged() {
    let input = "const amount = readPrice() - 0;";
    assert_eq_normalized(&apply(input), input);
}

// --- level gating (samples several families) ---------------------------------

#[test]
fn boolean_coercion_does_not_fire_below_aggressive() {
    let input = "const ok = !!flag;";
    assert_eq_normalized(&apply_standard(input), input);
}

#[test]
fn numeric_coercion_does_not_fire_below_aggressive() {
    let input = "const total = count * 1;";
    assert_eq_normalized(&apply_standard(input), input);
}

#[test]
fn string_coercion_does_not_fire_below_aggressive() {
    let input = "const out = `${value}`;";
    assert_eq_normalized(&apply_standard(input), input);
}
