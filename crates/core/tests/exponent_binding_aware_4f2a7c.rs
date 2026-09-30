mod common;

use common::{assert_eq_normalized, render_rule};
use wakaru_core::rules::Exponent;

fn apply(input: &str) -> String {
    render_rule(input, Exponent::new)
}

// --- globalThis spelling -----------------------------------------------------

#[test]
fn global_this_math_pow() {
    assert_eq_normalized(
        &apply("const x = globalThis.Math.pow(a, b);"),
        "const x = a ** b;",
    );
}

#[test]
fn window_math_pow_is_not_recovered() {
    // `window` is not guaranteed to be the global object (e.g. under Node).
    let input = "const x = window.Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn self_math_pow_is_not_recovered() {
    let input = "const x = self.Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

// --- alias recovery ----------------------------------------------------------

#[test]
fn const_object_alias() {
    let input = "const M = Math;\nconst x = M.pow(a, b);";
    let expected = "const M = Math;\nconst x = a ** b;";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn detached_method_alias() {
    let input = "const p = Math.pow;\nconst x = p(a, b);";
    let expected = "const p = Math.pow;\nconst x = a ** b;";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn destructured_method_alias() {
    let input = "const { pow } = Math;\nconst x = pow(a, b);";
    let expected = "const { pow } = Math;\nconst x = a ** b;";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn destructured_renamed_method_alias() {
    let input = "const { pow: p } = Math;\nconst x = p(a, b);";
    let expected = "const { pow: p } = Math;\nconst x = a ** b;";
    assert_eq_normalized(&apply(input), expected);
}

// --- alias non-matches -------------------------------------------------------

#[test]
fn let_alias_is_not_recovered() {
    // A `let` alias could be reassigned; only stable `const` aliases qualify.
    let input = "let M = Math;\nconst x = M.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn alias_of_non_math_is_not_recovered() {
    let input = "const M = notMath;\nconst x = M.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn detached_alias_of_other_method_is_not_recovered() {
    let input = "const p = Math.sqrt;\nconst x = p(a, b);";
    assert_eq_normalized(&apply(input), input);
}

// --- reassignment guards -----------------------------------------------------

#[test]
fn global_math_reassigned_blocks_recovery() {
    let input = "Math = fake;\nconst x = Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn math_pow_reassigned_blocks_recovery() {
    let input = "Math.pow = fn;\nconst x = Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn global_this_math_reassigned_blocks_recovery() {
    // Writing `globalThis.Math` changes the same slot as `Math`.
    let input = "globalThis.Math = fake;\nconst x = Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn math_update_blocks_recovery() {
    let input = "Math++;\nconst x = Math.pow(a, b);";
    assert_eq_normalized(&apply(input), input);
}

// --- shadowing ---------------------------------------------------------------

#[test]
fn mutation_of_shadowed_local_named_math_does_not_block() {
    // A *local* `Math` (parameter, different `SyntaxContext`) is not the global.
    let input = "function f(Math) {\n    Math = 1;\n}\nconst x = Math.pow(2, 3);";
    let expected = "function f(Math) {\n    Math = 1;\n}\nconst x = 2 ** 3;";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn shadowed_local_math_is_not_recovered() {
    let input = "function f(Math) {\n    return Math.pow(2, 3);\n}";
    assert_eq_normalized(&apply(input), input);
}

// --- argument-shape guards ---------------------------------------------------

#[test]
fn one_argument_is_not_recovered() {
    let input = "const x = Math.pow(2);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn three_arguments_is_not_recovered() {
    let input = "const x = Math.pow(2, 3, 4);";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn spread_argument_is_not_recovered() {
    let input = "const x = Math.pow(...args);";
    assert_eq_normalized(&apply(input), input);
}
