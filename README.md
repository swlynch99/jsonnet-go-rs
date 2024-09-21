# jsonnet-go

Run [jsonnet] programs in rust!

This crate provides idiomatic Rust bindings for the [go-jsonnet] library.

[jsonnet]: https://jsonnet.org
[go-jsonnet]: https://github.com/google/go-jsonnet

## Quick Start
Create a `JsonnetVm` and then call `evaluate_file` or `evaluate_snippet` to run
jsonnet code. These will return a string containing the resulting JSON:

```rust
use jsonnet_go::JsonnetVm;

fn main() -> jsonnet_go::Result<()> {
    let mut vm = JsonnetVm::new();
    let jsonnet = "{ field: std.base64('Hello, World!') }";
    let json = vm.evaluate_snippet("<inline>", jsonnet)?;

    println!("{json}");
    Ok(())
}
```

Alternatively, you could enable the `json` feature and use `evaluate_json` to
deserialize the returned JSON string:

```rust
use jsonnet_go::{JsonnetVm, EvaluateOptions};
use serde::Deserialize;

#[derive(Deserialize)]
struct Output {
    field: String
}

fn main() -> jsonnet_go::Result<()> {
    let mut vm = JsonnetVm::new();
    let jsonnet = "{ field: std.base64('Hello, World!') }";
    let options = EvaluateOptions::new("<inline>").snippet(jsonnet);
    let output: Output = vm.evaluate_json(options)?;

    assert_eq!(output.field, "SGVsbG8sIFdvcmxkIQ==");

    Ok(())
}
```

## Build Dependencies
You will need go 1.12+ installed in order to build go-jsonnet. You can install
it via:
- your package manager (e.g. apt install golang-go), or,
- the official install instructions at <https://go.dev/doc/install>.

On older distros the packaged version of go may not be new enough. In that case
you will need to install it from the official website.

## See Also
- The [jsonnet-rs] is a similar set of bindings for the libjsonnet C++ library.
  However, it has not been updated since jsonnet 0.17 and optimizations now
  mainly added to go-jsonnet and not libjsonnet.

[jsonnet-rs]: https://crates.io/crates/jsonnet-rs
