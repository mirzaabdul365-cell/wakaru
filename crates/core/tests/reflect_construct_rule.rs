mod common;

use common::{assert_eq_normalized, render_pipeline, render_pipeline_with_filename};

fn convert(input: &str) -> String {
    render_pipeline(input)
}

#[test]
fn converts_reflect_construct_for_standalone_constructors() {
    let output = convert(
        r#"
Reflect.construct(Ctor, args);
Reflect.construct(Ctor, [first, second]);
Reflect.construct(Ctor, []);
Reflect.construct(Ctor, [first, , third]);
Reflect.construct(Ctor, [first, ...rest]);
Reflect.construct(Ctor, ([first, second]));
Reflect.construct(eval, [source]);
"#,
    );

    assert_eq_normalized(
        &output,
        r#"
new Ctor(...args);
new Ctor(first, second);
new Ctor();
new Ctor(first, void 0, third);
new Ctor(first, ...rest);
new Ctor(first, second);
Reflect.construct(eval, [source]);
"#,
    );
}

#[test]
fn converts_three_argument_construct_with_identical_new_target() {
    let output = convert(
        r#"
const Ctor = base;
Reflect.construct(Ctor, args, Ctor);
Reflect.construct(Ctor, [first, second], Ctor);
Reflect.construct(Ctor, [first, ...rest], Ctor);
Reflect.construct(Ctor, args);
"#,
    );

    assert_eq_normalized(
        &output,
        r#"
const Ctor = base;
new Ctor(...args);
new Ctor(first, second);
new Ctor(first, ...rest);
new Ctor(...args);
"#,
    );
}

#[test]
fn preserves_three_argument_construct_when_new_target_is_not_identical() {
    let input = r#"
const Ctor = base;
let mutable = base;
Reflect.construct(Ctor, args, Other);
Reflect.construct(Ctor, args, void 0);
Reflect.construct(mutable, args, mutable);
Reflect.construct(namespace.Widget, args, namespace.Widget);
mutable = replacement;
"#;

    assert_eq_normalized(
        &convert(input),
        r#"
const Ctor = base;
let mutable = base;
Reflect.construct(Ctor, args, Other);
Reflect.construct(Ctor, args, undefined);
Reflect.construct(mutable, args, mutable);
Reflect.construct(namespace.Widget, args, namespace.Widget);
mutable = replacement;
"#,
    );
}

#[test]
fn converts_member_targets_with_stable_receivers() {
    let output = convert(
        r#"
const ns = lib;
Reflect.construct(ns.Widget, args);
Reflect.construct(ns[key], [first, second]);
Reflect.construct(this.Widget, args);
"#,
    );

    assert_eq_normalized(
        &output,
        r#"
const ns = lib;
new ns.Widget(...args);
new ns[key](first, second);
new this.Widget(...args);
"#,
    );
}

#[test]
fn preserves_member_targets_with_unstable_or_effectful_receivers() {
    let input = r#"
let obj = first;
Reflect.construct(obj.Widget, args);
Reflect.construct(getObject().Widget, args);
Reflect.construct(getObject()[key()], args);
obj = second;
"#;

    assert_eq_normalized(
        &convert(input),
        r#"
let obj = first;
Reflect.construct(obj.Widget, args);
Reflect.construct(getObject().Widget, args);
Reflect.construct(getObject()[key()], args);
obj = second;
"#,
    );
}

#[test]
fn distinguishes_namespace_and_live_import_receivers() {
    let output = convert(
        r#"
import * as namespace from "./dependency";
import { receiver } from "./dependency";
Reflect.construct(namespace.Widget, args);
Reflect.construct(receiver.Widget, args);
"#,
    );

    assert_eq_normalized(
        &output,
        r#"
import * as namespace from "./dependency";
import { receiver } from "./dependency";
new namespace.Widget(...args);
Reflect.construct(receiver.Widget, args);
"#,
    );
}

#[test]
fn preserves_direct_spread_in_construct_arguments() {
    assert_eq_normalized(
        &convert(
            "Reflect.construct(...target, args);\nReflect.construct(Ctor, ...args);\nReflect.construct(Ctor, [first, ...rest]);\nReflect.construct(Ctor, args);",
        ),
        "Reflect.construct(...target, args);\nReflect.construct(Ctor, ...args);\nnew Ctor(first, ...rest);\nnew Ctor(...args);",
    );
}

#[test]
fn preserves_shadowed_reflect() {
    assert_eq_normalized(
        &convert(
            "function wrapper(Reflect) { return Reflect.construct(Ctor, args); }\n{ const Reflect = custom; Reflect.construct(Ctor, args); }\nwith ({ Reflect: { construct() { sideEffect(); } } }) { Reflect.construct(Ctor, args); }\nReflect.construct(Ctor, args);",
        ),
        "function wrapper(Reflect) { return Reflect.construct(Ctor, args); }\n{ const Reflect = custom; Reflect.construct(Ctor, args); }\nwith ({ Reflect: { construct() { sideEffect(); } } }) { Reflect.construct(Ctor, args); }\nnew Ctor(...args);",
    );
}

#[test]
fn preserves_reflect_only_inside_direct_eval_scopes() {
    assert_eq_normalized(
        &convert(
            r#"
function dynamic(Ctor, args) {
    eval("var Reflect = custom");
    return Reflect.construct(Ctor, args);
}
class Holder {
    value = eval("");
}
function unused() { eval(""); }
Reflect.construct(Ctor, args);
"#,
        ),
        r#"
function dynamic(Ctor, args) {
    eval("var Reflect = custom");
    return Reflect.construct(Ctor, args);
}
class Holder {
    value = eval("");
}
function unused() { eval(""); }
new Ctor(...args);
"#,
    );
}

#[test]
fn covers_transparent_typescript_argument_wrappers() {
    let output = render_pipeline_with_filename(
        r#"
Reflect.construct(Ctor, ([first, second] as unknown[]));
Reflect.construct(Ctor, (<unknown[]>[first, second]));
Reflect.construct(Ctor, args);
"#,
        "fixture.ts",
    );

    assert_eq_normalized(
        &output,
        r#"
new Ctor(first, second);
new Ctor(first, second);
new Ctor(...args);
"#,
    );
}
