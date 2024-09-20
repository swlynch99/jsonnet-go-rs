use jsonnet_go::*;

#[test]
fn evaluate_base64() {
    let jsonnet = "std.base64('Hello, World!')";
    let mut vm = JsonnetVm::new();
    let json = vm
        .evaluate_snippet("<test>", jsonnet)
        .expect("failed to evaluate the snippet");

    assert_eq!(json.trim(), "\"SGVsbG8sIFdvcmxkIQ==\"");
}
