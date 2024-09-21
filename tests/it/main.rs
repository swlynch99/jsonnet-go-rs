use jsonnet_go::*;

#[cfg(feature = "json")]
mod json;

#[test]
fn evaluate_base64() {
    let jsonnet = "std.base64('Hello, World!')";
    let mut vm = JsonnetVm::new();
    let json = vm
        .evaluate_snippet("<test>", jsonnet)
        .expect("failed to evaluate the snippet");

    assert_eq!(json.trim(), "\"SGVsbG8sIFdvcmxkIQ==\"");
}

#[test]
fn version_is_valid_utf8() {
    let _ = version();
}

#[test]
fn import_callback() -> anyhow::Result<()> {
    use std::path::{Path, PathBuf};

    use jsonnet_go::{EvaluateOptions, JsonnetVm};
    let mut vm = JsonnetVm::new();
    vm.import_callback(|_, base, rel| {
        if rel == Path::new("data.libsonnet") {
            return Ok((
                PathBuf::from("data.libsonnet"),
                br#" "Here's the file contents!" "#.to_vec(),
            ));
        }

        Err(format!("could not import `{}`", base.join(rel).display()))
    });

    let jsonnet = r#"
local data = import "data.libsonnet";

"the data was: " + data
"#;

    let options = EvaluateOptions::new("<example 6>")
        .snippet(jsonnet)
        .string_output(true);
    let output = vm.evaluate(options)?;

    assert_eq!(output, "the data was: Here's the file contents!");
    Ok(())
}

#[test]
fn native_callback() -> anyhow::Result<()> {
    let mut vm = JsonnetVm::new();
    vm.native_callback("cbrt", ["x"], |vm, args| {
        if args.len() != 1 {
            return Err(format!("expected 1 argument, got {} instead", args.len()));
        }

        let Some(x) = args[0].as_number() else {
            return Err("argument was of the wrong type, expected a number".into());
        };

        Ok(JsonValue::number(vm, x.cbrt()))
    });

    let jsonnet = r#"
local cbrt = std.native("cbrt");
cbrt(8)
"#;

    let output = vm.evaluate_snippet("<example 7>", jsonnet)?;
    let output: f64 = output.parse()?;

    assert!((output - 2.0).abs() < 1e-10, "2.0 != {output}");
    Ok(())
}

// This is currently not implemented in go-jsonnet
#[test]
#[should_panic]
fn native_callback_failure() {
    let mut vm = JsonnetVm::new();
    vm.native_callback("testfn", ["x"], |_, _| {
        Err("test function failed (test string 0xDEADBEEF)".into())
    });

    let jsonnet = r#"std.native("testfn")("testing")"#;
    let error = vm
        .evaluate_snippet("<test>", jsonnet)
        .expect_err("test case failed to error");
    let message = error.to_string();

    assert!(
        message.contains("(test string 0xDEADBEEF)"),
        "error message did not contain test string:\n{message}"
    );
}
