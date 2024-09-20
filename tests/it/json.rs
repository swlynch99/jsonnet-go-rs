use jsonnet_go::{EvaluateOptions, JsonnetVm};
use serde::{Deserialize, Serialize};

const TEST_PROGRAM: &'static str = r#"std.extVar('value')"#;

#[test]
fn ext_string() {
    let mut vm = JsonnetVm::new();
    let text = "here's a test string!";

    vm.ext_json("value", text).unwrap();
    let output = vm
        .evaluate(
            EvaluateOptions::new("<test>".as_ref())
                .snippet(TEST_PROGRAM)
                .string_output(true),
        )
        .expect("failed to evaluate the test program");

    assert_eq!(output, text);
}

#[test]
fn ext_string_weird() {
    let mut vm = JsonnetVm::new();
    let text = "\
  escaped quote: \\\"
unescaped quote: \"
   single quote: '
";

    vm.ext_json("value", text).unwrap();
    let output = match vm.evaluate(
        EvaluateOptions::new("<test>".as_ref())
            .snippet(TEST_PROGRAM)
            .string_output(true),
    ) {
        Ok(output) => output,
        Err(e) => panic!("failed to evaluate the test program:\n{e}"),
    };

    assert_eq!(output, text);
}

#[test]
fn ext_complex() {
    #[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
    struct Complex {
        data: String,
        number: i32,
        option: Option<u64>,
        null: (),
        boolean: bool,
    }

    let value = Complex {
        data: "a data string".into(),
        number: -5,
        option: Some(77),
        null: (),
        boolean: false,
    };

    let mut vm = JsonnetVm::new();
    vm.ext_json("value", &value).unwrap();

    let options = EvaluateOptions::new("<test>".as_ref()).snippet(TEST_PROGRAM);
    let output: Complex = match vm.evaluate_json(options) {
        Ok(output) => output,
        Err(e) => panic!("failed to evaluate the test program:\n{e}"),
    };

    assert_eq!(output, value);
}
