mod common;

use common::{assert_eq_normalized, render_rule};
use wakaru_core::rules::RemoveVoid;

fn apply(input: &str) -> String {
    render_rule(input, RemoveVoid::new)
}

// --- converts where `undefined` is the global --------------------------------

#[test]
fn converts_at_module_scope() {
    assert_eq_normalized(&apply("const a = void 0;"), "const a = undefined;");
}

#[test]
fn converts_inside_plain_function() {
    assert_eq_normalized(
        &apply("function f() {\n    return void 0;\n}"),
        "function f() {\n    return undefined;\n}",
    );
}

#[test]
fn converts_inside_plain_block() {
    assert_eq_normalized(
        &apply("{\n    const a = void 0;\n}"),
        "{\n    const a = undefined;\n}",
    );
}

// --- preserves where `undefined` is shadowed ---------------------------------

#[test]
fn preserves_under_parameter_named_undefined() {
    let input = "function f(undefined) {\n    return void 0;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_arrow_parameter_named_undefined() {
    let input = "const f = (undefined)=>void 0;";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_hoisted_var_undefined() {
    // `var undefined` hoists over the whole function, so even the earlier
    // `void 0` must be preserved.
    let input = "function f() {\n    const a = void 0;\n    var undefined = 1;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_block_scoped_let_undefined() {
    let input = "{\n    let undefined = 1;\n    const a = void 0;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_catch_binding_named_undefined() {
    let input = "try {} catch (undefined) {\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_inside_with_block() {
    let input = "with (o) {\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_inside_function_with_direct_eval() {
    let input = "function f(s) {\n    eval(s);\n    return void 0;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_module_level_var_undefined() {
    let input = "var undefined = 1;\nconst a = void 0;";
    assert_eq_normalized(&apply(input), input);
}

// --- scope precision: shadowing is local -------------------------------------

#[test]
fn shadow_in_one_function_does_not_block_a_sibling() {
    let input =
        "function shadowed(undefined) {\n    return void 0;\n}\nfunction clean() {\n    return void 0;\n}";
    let expected =
        "function shadowed(undefined) {\n    return void 0;\n}\nfunction clean() {\n    return undefined;\n}";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn shadow_in_nested_scope_does_not_block_module_scope() {
    let input = "const a = void 0;\nfunction f(undefined) {\n    return void 0;\n}";
    let expected = "const a = undefined;\nfunction f(undefined) {\n    return void 0;\n}";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn shadow_in_block_does_not_block_enclosing_scope() {
    let input = "const a = void 0;\n{\n    let undefined = 1;\n    const b = void 0;\n}";
    let expected = "const a = undefined;\n{\n    let undefined = 1;\n    const b = void 0;\n}";
    assert_eq_normalized(&apply(input), expected);
}

#[test]
fn eval_in_one_function_does_not_block_a_sibling() {
    let input = "function tainted(s) {\n    eval(s);\n}\nfunction clean() {\n    return void 0;\n}";
    let expected =
        "function tainted(s) {\n    eval(s);\n}\nfunction clean() {\n    return undefined;\n}";
    assert_eq_normalized(&apply(input), expected);
}

// --- existing guards still hold ----------------------------------------------

#[test]
fn does_not_touch_delete_operand() {
    let input = "delete void 0;";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn does_not_touch_void_with_effectful_operand() {
    let input = "const x = void f();";
    assert_eq_normalized(&apply(input), input);
}

// --- named function expression (binds its own name in its scope) --------------

#[test]
fn preserves_inside_named_function_expression_undefined() {
    let input = "const f = function undefined() {\n    return void 0;\n};";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn named_function_expression_does_not_block_outer_scope() {
    let input = "const a = void 0;\nconst f = function undefined() {\n    return void 0;\n};";
    let expected = "const a = undefined;\nconst f = function undefined() {\n    return void 0;\n};";
    assert_eq_normalized(&apply(input), expected);
}

// --- for-head bindings -------------------------------------------------------

#[test]
fn preserves_under_for_of_head_binding() {
    let input = "for (let undefined of xs){\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_for_in_head_binding() {
    let input = "for (let undefined in o){\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_c_style_for_head_binding() {
    let input = "for(let undefined = 0; undefined < n; undefined++){\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn for_head_shadow_does_not_block_enclosing_scope() {
    let input = "const a = void 0;\nfor (let undefined of xs){\n    const b = void 0;\n}";
    let expected = "const a = undefined;\nfor (let undefined of xs){\n    const b = void 0;\n}";
    assert_eq_normalized(&apply(input), expected);
}

// --- further shadow forms ----------------------------------------------------

#[test]
fn preserves_under_tdz_before_let_undefined() {
    // The `void 0` precedes the `let undefined` but is still in that block's
    // scope (temporal dead zone), so it must be preserved.
    let input = "{\n    const a = void 0;\n    let undefined = 1;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_destructured_parameter_undefined() {
    let input = "function f({ undefined }) {\n    return void 0;\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_destructured_catch_binding_undefined() {
    let input = "try {} catch ({ undefined }) {\n    console.log(void 0);\n}";
    assert_eq_normalized(&apply(input), input);
}

#[test]
fn preserves_under_module_level_class_named_undefined() {
    let input = "class undefined {}\nconst a = void 0;";
    assert_eq_normalized(&apply(input), input);
}
