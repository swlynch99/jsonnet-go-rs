//! Idiomatic rust bindings for the [go-jsonnet] C API.
//!
//! [go-jsonnet]: https://github.com/google/go-jsonnet
//!
//! # Quick Start
//! Create a [`JsonnetVm`] and then call [`evaluate_file`] or
//! [`evaluate_snippet`] to run jsonnet code. These will return a string
//! containing the resulting JSON.
//!
//! ```
//! # use jsonnet_go::JsonnetVm;
//! #
//! # fn main() -> anyhow::Result<()> {
//! let jsonnet = "{ field: std.base64('Hello, World!') }";
//! let mut vm = JsonnetVm::new();
//!
//! let json = vm.evaluate_snippet("test.jsonnet", jsonnet)?;
//! # Ok(())
//! # }
//! ```
//!
//! For more control you can use [`EvaluateOptions`] to set both the filename
//! and (optionally) the snippet to be evaluated.
//!
//! ```
//! # use jsonnet_go::{JsonnetVm, EvaluateOptions};
//! # fn main() -> anyhow::Result<()> {
//! let jsonnet = "{ field: std.base64('Hello, World!') }";
//! let mut vm = JsonnetVm::new();
//!
//! let options = EvaluateOptions::new("<example 2>").snippet(jsonnet);
//! let json = vm.evaluate(options)?;
//! # Ok(())
//! # }
//! ```
//!
//! For details on how to write jsonnet programs see <https://jsonnet.org> or
//! one of the documentation pages on that same site:
//! - the jsonnet tutorial: <https://jsonnet.org/learning/tutorial.html>
//! - the jsonnet standard library docs: <https://jsonnet.org/ref/stdlib.html>
//! - the jsonnet language reference: <https://jsonnet.org/ref/language.html>
//!
//! [`evaluate_file`]: JsonnetVm::evaluate_file
//! [`evaluate_snippet`]: JsonnetVm::evaluate_snippet
//!
//! # Passing external values to Jsonnet programs
//! Jsonnet provides two different ways to pass external values to a jsonnet
//! program (beyond, say, importing a json file at a known path).
//!
//! ## Top-Level Arguments (TLAs)
//! Jsonnet allows the top-level expression in a file to be a function
//! definition instead of a JSON object. If it is a function, then the arguments
//! to that function are called top-level arguments and can be provided by the
//! jsonnet runtime.
//!
//! To set the top-level arguments for a jsonnet program, use
//! [`JsonnetVm::tla_var`], [`JsonnetVm::tla_code`], or, if the `json` feature
//! is enabled, [`JsonnetVm::tla_json`].
//!
//! ```
//! # use jsonnet_go::{JsonnetVm, EvaluateOptions};
//! # fn main() -> anyhow::Result<()> {
//! let jsonnet = r#"
//! function(count, message = "Testing, 1, 2,")
//!     std.format("%s ..., %d", [message, count])
//! "#;
//!
//! let mut vm = JsonnetVm::new();
//! vm.tla_code("count", "17");
//!
//! let options = EvaluateOptions::new("<example 3>")
//!     .snippet(jsonnet)
//!     .string_output(true);
//! let output = vm.evaluate(options)?;
//!
//! assert_eq!(output, "Testing, 1, 2, ..., 17");
//! # Ok(())
//! # }
//! ```
//!
//! The main advantage of TLAs is that they allow defaults to be provided. In
//! the example above, no value was set for the `message` TLA so it used the
//! default. If we had not provided a `count` TLA, though, then running the
//! program would have exited with an error.
//!
//! ## External Variables (ExtVars)
//! The jsonnet standard library provides the [`std.extVar`] function. This
//! allows a jsonnet program to access extvars set by the runtime. Unlike with
//! TLAs, however, if [`std.extVar`] is called with a name that is not defined
//! then that results in an immediate error with no way to recover.
//!
//! ExtVars can be set by calling [`JsonnetVm::ext_var`],
//! [`JsonnetVm::ext_code`], or, if the `json` feature is enabled,
//! [`JsonnetVm::ext_json`].
//!
//! ```
//! # use jsonnet_go::{JsonnetVm, EvaluateOptions};
//! # fn main() -> anyhow::Result<()> {
//! let jsonnet = r#"
//! std.format("Testing 1, 2, ..., %d", [std.extVar('count')])
//! "#;
//!
//! let mut vm = JsonnetVm::new();
//! vm.ext_code("count", "17");
//!
//! let options = EvaluateOptions::new("<example 4>")
//!     .snippet(jsonnet)
//!     .string_output(true);
//! let output = vm.evaluate(options)?;
//!
//! assert_eq!(output, "Testing 1, 2, ..., 17");
//! # Ok(())
//! # }
//! ```
//!
//! ExtVars have the advantage that they don't need to be threaded down through
//! the program into libraries and such. However, the tradeoff is that
//! attempting to access an extvar that doesn't exist results in an immediate
//! error.
//!
//! [`std.extVar`]: https://jsonnet.org/ref/stdlib.html#ext_vars
//!
//! # Integration with `serde_json`
//! If the `json` feature is enabled then this crate can take care of converting
//! rust values to and from JSON. You can use [`JsonnetVm::evaluate_json`] to
//! run a jsonnet program and get its output as a rust type in one step. You can
//! also use [`JsonnetVm::tla_json`] and [`JsonnetVm::ext_json`] to set
//! top-level arguments and external variables to JSON values, which is
//! otherwise somewhat finicky to do.
//!
//! ```
//! # #[cfg(feature = "json")] fn main() -> anyhow::Result<()> {
//! # use jsonnet_go::{JsonnetVm, EvaluateOptions};
//! # use serde::{Serialize, Deserialize};
//! #[derive(Serialize, Deserialize)]
//! struct Output {
//!     version: u64,
//!     values: Vec<String>,
//! }
//!
//! let jsonnet = r#"
//! function(version) {
//!     version: version + 2,
//!     values: std.extVar("values")
//! }
//! "#;
//!
//! let mut vm = JsonnetVm::new();
//! vm.tla_json("version", &5)?;
//! vm.ext_json("values", &vec!["three", "whole", "strings"]);
//!
//! let options = EvaluateOptions::new("<example 5>").snippet(jsonnet);
//! let output: Output = vm.evaluate_json(options)?;
//!
//! assert_eq!(output.version, 7);
//! assert_eq!(output.values, vec!["three", "whole", "strings"]);
//! # Ok(())
//! # }
//! # #[cfg(not(feature = "json"))] fn main() {}
//! ```
//!
//! # Custom Import Callbacks
//! Jsonnet allows external files to be imported via `import`, `importstr`, and
//! `importbin`. By default, it looks in the same directory as the file which
//! contained the `import` statement followed by looking in all the paths
//! specified via [`JsonnetVm::jpath_add`].
//!
//! If this is not the behaviour you want then you can override the import
//! callback used by the jsonnet VM via [`JsonnetVm::import_callback`]. This
//! will be called when an import statement is evaluated and is responsible for
//! returning both the path and content of the file, if it is sucessfully
//! imported.
//!
//! ```
//! # use jsonnet_go::{JsonnetVm, EvaluateOptions};
//! # use std::path::{Path, PathBuf};
//! # fn main() -> anyhow::Result<()> {
//! let mut vm = JsonnetVm::new();
//! vm.import_callback(|vm, base, rel| {
//!     if rel == Path::new("data.libsonnet") {
//!         return Ok((
//!             PathBuf::from("data.libsonnet"),
//!             br#" "Here's the file contents!" "#.to_vec(),
//!         ));
//!     }
//!
//!     Err(format!("could not import `{}`", base.join(rel).display()))
//! });
//!
//! let jsonnet = r#"
//! local data = import "data.libsonnet";
//!
//! "the data was: " + data
//! "#;
//!
//! let options = EvaluateOptions::new("<example 6>")
//!     .snippet(jsonnet)
//!     .string_output(true);
//! let output = vm.evaluate(options)?;
//!
//! assert_eq!(output, "the data was: Here's the file contents!");
//! # Ok(())
//! # }
//! ```
//!
//! # Native Extensions
//! Jsonnet allows for providing native extensions. These are rust functions
//! which are registered with the runtime which can then be accessed via jsonnet
//! programs via the `std.nativeExt` function.
//!
//! To declare a new native extension, call [`JsonnetVm::native_callback`] with
//! the native function you want to provide.
//!
//! ```
//! # fn main() -> anyhow::Result<()> {
//! # use jsonnet_go::{JsonnetVm, JsonValue};
//! let mut vm = JsonnetVm::new();
//! vm.native_callback("cbrt", ["x"], |vm, args| {
//!     if args.len() != 1 {
//!         return Err(format!("expected 1 argument, got {} instead", args.len()));
//!     }
//!
//!     let Some(x) = args[0].as_number() else {
//!         return Err("argument was of the wrong type, expected a number".into());
//!     };
//!
//!     Ok(JsonValue::number(vm, x.cbrt()))
//! });
//!
//! let jsonnet = r#"
//! local cbrt = std.native("cbrt");
//! cbrt(8)
//! "#;
//!
//! let output = vm.evaluate_snippet("<example 7>", jsonnet)?;
//! let output: f64 = output.parse()?;
//!
//! assert!((output - 2.0).abs() < 1e-10, "2.0 != {output}");
//! # Ok(())
//! # }
//! ```
//!
//! # Features
//! The following features are available:
//! - `serde` - Enables the [`serde`] module. This is likely to only be useful
//!   if you are writing native extensions.
//! - `json`  - Enables helper methods that require [`serde_json`]. That is,
//!   [`JsonnetVm::evaluate_json`], [`JsonnetVm::tla_json`], and
//!   [`JsonnetVm::ext_json`].
//!
//! # Caveats and Footguns
//! This library is built on the C interface to go-jsonnet. Unfortunately, that
//! interface comes with some caveats:
//! - Nul bytes in strings passed in as parameters will result in a panic.
//! - Nul bytes in strings returned from the jsonnet VM will result in the
//!   output getting silently truncated. This is somewhat difficult to do,
//!   although likely still possible.

#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![warn(missing_docs)]

use std::collections::BTreeMap;
use std::ffi::{c_char, c_int, c_void, CStr, CString, OsStr};
use std::fmt;
use std::iter::FusedIterator;
use std::mem::ManuallyDrop;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::str::Utf8Error;

#[cfg(feature = "json")]
use ::serde::{de::DeserializeOwned, Serialize};
use jsonnet_go_sys as sys;

use crate::string::JsonnetStringBuilder;

mod string;
mod value;

#[cfg(feature = "serde")]
pub mod serde;

pub use crate::string::JsonnetString;
pub use crate::value::{AsJsonVal, JsonVal, JsonValue};

/// Result type returned by jsonnet methods.
pub type Result<T, E = Error> = std::result::Result<T, E>;

/// The Jsonnet VM.
///
/// It allows you to run Jsonnet programs and is also responsible for managing
/// the memory of all values involved within the program, along with imports and
/// native extensions.
///
/// See the [`crate`] documentation for more details.
pub struct JsonnetVm {
    vm: NonNull<sys::JsonnetVm>,

    /// Callback data for the import callback.
    ///
    /// This ensures that we can drop it when we are dropped or when a new
    /// import callback is raised.
    import_cb_data: Box<dyn Send>,

    /// Callback data for native callbacks.
    native_cb_data: BTreeMap<CString, Box<dyn Send>>,
}

impl JsonnetVm {
    /// Create a new Jsonnet VM.
    pub fn new() -> Self {
        unsafe { Self::from_raw(sys::jsonnet_make()) }
    }

    /// Create a new `JsonnetVm` from a raw [`sys::JsonnetVm`].
    ///
    /// # Safety
    /// `vm` must have been returned from a [`sys::jsonnet_make`] call.
    pub unsafe fn from_raw(vm: *mut sys::JsonnetVm) -> Self {
        debug_assert!(!vm.is_null());

        Self {
            vm: unsafe { NonNull::new_unchecked(vm) },
            import_cb_data: Box::new(()),
            native_cb_data: BTreeMap::new(),
        }
    }

    /// Get the raw [`sys::JsonnetVm`] pointer.
    pub fn as_raw(&self) -> *mut sys::JsonnetVm {
        self.vm.as_ptr()
    }

    /// Convert this VM in to the raw underlying [`sys::JsonnetVm`] pointer.
    ///
    /// This method leaks the data associated with the register VM callbacks.
    pub fn into_raw(self) -> *mut sys::JsonnetVm {
        // Note: We need to leak the callback data since it will continue to be
        //       referenced by the VM.
        let this = ManuallyDrop::new(self);

        this.vm.as_ptr()
    }

    /// Set the maximum stack depth.
    pub fn max_stack(&mut self, max_stack: u32) {
        unsafe { sys::jsonnet_max_stack(self.as_raw(), max_stack) };
    }

    /// Set the number of objects required before a garbage collection cycle is
    /// allowed.
    pub fn gc_min_objects(&mut self, min_objects: u32) {
        unsafe { sys::jsonnet_gc_min_objects(self.as_raw(), min_objects) }
    }

    /// Run the garbage collector after this amount of growth in the number of
    /// objects.
    pub fn gc_growth_trigger(&mut self, value: f64) {
        unsafe { sys::jsonnet_gc_growth_trigger(self.as_raw(), value) }
    }

    /// Indicate that the VM should expect a string output and return that
    /// directly instead of JSON encoding it.
    ///
    /// This is not public since it is set via [`EvaluateOptions`] for a single
    /// call.
    fn string_output(&mut self, value: bool) {
        unsafe { sys::jsonnet_string_output(self.as_raw(), value.into()) }
    }

    /// Set the callback used to locate imports.
    ///
    /// The callback takes the following parameters:
    /// - `vm`   - A handle to the [`JsonnetVm`] it was registered with.
    /// - `base` - The path to the directory containing the code that did the
    ///   import.
    /// - `rel`  - The path imported by the code.
    ///
    /// It should return either a tuple containing the path at which the file
    /// was found, and its contents, or an error message explaining why it could
    /// not be found.
    pub fn import_callback<F, E>(&mut self, cb: F)
    where
        F: Fn(&JsonnetVm, &Path, &Path) -> Result<(PathBuf, Vec<u8>), E>,
        F: Send + Sync + 'static,
        E: fmt::Display,
    {
        struct ImportContext<F> {
            vm: NonNull<sys::JsonnetVm>,
            cb: F,
        }

        unsafe impl<F: Send> Send for ImportContext<F> {}

        extern "C" fn callback<F, E>(
            ctx: *mut c_void,
            base: *const c_char,
            rel: *const c_char,
            found_here: *mut *mut c_char,
            buf: *mut *mut c_char,
            buflen: *mut usize,
        ) -> c_int
        where
            F: Fn(&JsonnetVm, &Path, &Path) -> Result<(PathBuf, Vec<u8>), E>,
            E: fmt::Display,
        {
            use std::fmt::Write;

            let ctx = unsafe { &*(ctx as *const c_void as *const ImportContext<F>) };

            // We need ManuallyDrop here so that the VM is not freed.
            let vm = ManuallyDrop::new(unsafe { JsonnetVm::from_raw(ctx.vm.as_ptr()) });

            let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                let base = unsafe { CStr::from_ptr(base) };
                let base = match bytes_to_osstr(base.to_bytes()) {
                    Ok(base) => Path::new(base),
                    Err(e) => {
                        let error = format!("base path contained invalid utf8: {e}");
                        let error = JsonnetString::from_str(&vm, &error);

                        unsafe {
                            *buflen = error.capacity();
                            *buf = error.into_raw();
                        }

                        return 1;
                    }
                };

                let rel = unsafe { CStr::from_ptr(rel) };
                let rel = match bytes_to_osstr(rel.to_bytes()) {
                    Ok(rel) => Path::new(rel),
                    Err(e) => {
                        let mut error = JsonnetStringBuilder::with_capacity(&vm, 128);
                        let _ = write!(&mut error, "relative path contained invalid utf8: {e}");
                        let error = error.into_string();

                        unsafe {
                            *buflen = error.capacity();
                            *buf = error.into_raw();
                        }

                        return 1;
                    }
                };

                match (ctx.cb)(&vm, base, rel) {
                    Ok((location, content)) => unsafe {
                        let location =
                            JsonnetString::from_bytes(&vm, location.as_os_str().as_encoded_bytes());

                        let mem =
                            sys::jsonnet_realloc(vm.as_raw(), std::ptr::null_mut(), content.len())
                                as *mut u8;
                        std::ptr::copy_nonoverlapping(content.as_ptr(), mem, content.len());

                        *buf = mem as *mut _;
                        *buflen = content.len();
                        *found_here = location.into_raw();

                        0
                    },
                    Err(e) => {
                        let error = JsonnetString::from_str(&vm, &e.to_string());

                        unsafe {
                            *buflen = error.capacity();
                            *buf = error.into_raw();
                        }

                        1
                    }
                }
            }));

            match result {
                Ok(result) => result,
                Err(payload) => unsafe {
                    let message: &str = if let Some(message) = payload.downcast_ref::<String>() {
                        message
                    } else if let Some(message) = payload.downcast_ref::<&str>() {
                        message
                    } else {
                        "Box<dyn Any>"
                    };

                    let mut error = JsonnetStringBuilder::with_capacity(&vm, 128);
                    error.push_str("import callback panicked: ");
                    error.push_str(message);

                    let message = error.into_string();

                    *buflen = message.capacity();
                    *buf = message.into_raw();

                    1
                },
            }
        }

        let mut context = Box::new(ImportContext { vm: self.vm, cb });

        unsafe {
            sys::jsonnet_import_callback(
                self.as_raw(),
                Some(callback::<F, E>),
                context.as_mut() as *mut _ as *mut c_void,
            );
        }

        self.import_cb_data = context;
    }

    /// Add a callback to provide a native extension to Jsonnet.
    ///
    /// This will appear in Jsonnet as a function type and can be accessed via
    /// `std.nativeExt`.
    ///
    /// # Side Effects
    /// Do not register native callbacks with side-effects! Jsonnet is a lazy
    /// functional language and will tall your function when you least expect
    /// it, more times than you expect, or not at all.
    ///
    /// # Parameters
    /// - `name`   - The name of the function as visible to jsonnet code. This
    ///   is what you provide to `std.nativeExt` to get at the function.
    /// - `params` - The names of the parameters. These must be valid Jsonnet
    ///   identifiers.
    /// - `cb` - The callback itself.
    ///
    /// # Panics
    /// This function will panic if `name` or any of the parameter names contain
    /// a nul byte.
    pub fn native_callback<'a, F>(
        &mut self,
        name: &str,
        params: impl IntoIterator<Item = &'a str>,
        cb: F,
    ) where
        F: for<'vm> Fn(&'vm JsonnetVm, &[JsonVal<'vm, 'vm>]) -> Result<JsonValue<'vm>, String>,
        F: Send + Sync + 'static,
    {
        struct NativeContext<F> {
            vm: NonNull<sys::JsonnetVm>,
            cb: F,
        }

        unsafe impl<F: Send> Send for NativeContext<F> {}

        extern "C" fn callback<F>(
            ctx: *mut c_void,
            argv: *const *const sys::JsonnetJsonValue,
            success: *mut c_int,
        ) -> *mut sys::JsonnetJsonValue
        where
            F: for<'vm> Fn(&'vm JsonnetVm, &[JsonVal<'vm, 'vm>]) -> Result<JsonValue<'vm>, String>,
            F: Send + Sync + 'static,
        {
            let ctx = unsafe { &mut *(ctx as *mut NativeContext<F>) };
            let vm = unsafe { ManuallyDrop::new(JsonnetVm::from_raw(ctx.vm.as_ptr())) };

            let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
                let mut values = Vec::new();
                let mut current = argv;

                // SAFETY: argv is a null-terminated array of arguments. We loop over them until
                //         we find a null pointer.
                unsafe {
                    while !(*current).is_null() {
                        values.push(JsonVal::new(&vm, &**current));
                        current = current.add(1);
                    }
                }

                match (ctx.cb)(&vm, &values) {
                    Ok(value) => {
                        unsafe { *success = 1 };
                        value
                    }
                    Err(e) => {
                        unsafe { *success = 0 };
                        JsonValue::string(&vm, &e)
                    }
                }
            }));

            match result {
                Ok(value) => value.into_raw(),
                Err(payload) => {
                    let message: &str = if let Some(message) = payload.downcast_ref::<String>() {
                        message
                    } else if let Some(message) = payload.downcast_ref::<&str>() {
                        message
                    } else {
                        "Box<dyn Any>"
                    };

                    let message = format!("native callback panicked: {message}");
                    let message = JsonValue::string(&vm, &message);

                    unsafe { *success = 0 };
                    message.into_raw()
                }
            }
        }

        let mut ctx = Box::new(NativeContext { vm: self.vm, cb });

        let name = str_to_cstring(name);
        let params: Vec<_> = params.into_iter().map(str_to_cstring).collect();
        let params: Vec<_> = params
            .iter()
            .map(|p| p.as_ptr())
            .chain(std::iter::once(std::ptr::null()))
            .collect();

        unsafe {
            sys::jsonnet_native_callback(
                self.as_raw(),
                name.as_ptr(),
                Some(callback::<F>),
                ctx.as_mut() as *mut _ as *mut c_void,
                params.as_ptr(),
            );
        }

        self.native_cb_data.insert(name, ctx);
    }

    /// Bind a jsonnet external variable to the given string.
    ///
    /// See the jsonnet language reference section on [external variables][0]
    /// for more details on external variables.
    ///
    /// [0]: https://jsonnet.org/ref/language.html#external-variables-extvars
    ///
    /// # Panics
    /// This method panics if either of `key` or `value` contain a nul byte.
    pub fn ext_var(&mut self, key: &str, val: &str) {
        let key = str_to_cstring(key);
        let val = str_to_cstring(val);

        unsafe { sys::jsonnet_ext_var(self.as_raw(), key.as_ptr(), val.as_ptr()) }
    }

    /// Bind a jsonnet external variable to the result of the provided code
    /// snippet.
    ///
    /// See the jsonnet language reference section on [external variables][0]
    /// for more details on external variables.
    ///
    /// [0]: https://jsonnet.org/ref/language.html#external-variables-extvars
    ///
    /// # Panics
    /// This method panics if either of `key` or `value` contain a nul byte.
    pub fn ext_code(&mut self, key: &str, value: &str) {
        let key = str_to_cstring(key);
        let val = str_to_cstring(value);

        unsafe { sys::jsonnet_ext_code(self.as_raw(), key.as_ptr(), val.as_ptr()) }
    }

    /// Bind a jsonnet external variable to a provided json value.
    ///
    /// See the jsonnet language reference section on [external variables][0]
    /// for more details on external variables.
    ///
    /// [0]: https://jsonnet.org/ref/language.html#external-variables-
    ///
    /// # Errors
    /// This method will only return an error if the serialization of `value`
    /// returns an error.
    ///
    /// # Panics
    /// This method panics if either of `key` or the serialized JSON form of
    /// `value` contain a nul byte.
    #[cfg(feature = "json")]
    pub fn ext_json<V>(&mut self, key: &str, value: &V) -> serde_json::Result<()>
    where
        V: Serialize + ?Sized,
    {
        let json = serde_json::to_string(value)?;

        let mut code = String::with_capacity(json.len() + 32);
        code.push_str("std.parseJson(");
        jsonnet_escape(&json, &mut code)?;
        code.push(')');

        self.ext_code(key, &code);
        Ok(())
    }

    /// Bind a string top-level argument for a top-level parameter.
    ///
    /// See the jsonnet language reference for details on what a top-level
    /// argument is. Specifically, see the section on [top-level arguments][0]
    ///
    /// [0]: https://jsonnet.org/ref/language.html#top-level-arguments-tlas
    ///
    /// # Panics
    /// This method panics if either of `key` or `value` contain a nul byte.
    pub fn tla_var(&mut self, key: &str, val: &str) {
        let key = str_to_cstring(key);
        let val = str_to_cstring(val);

        unsafe { sys::jsonnet_tla_var(self.as_raw(), key.as_ptr(), val.as_ptr()) }
    }

    /// Bind a top-level argument to the output of a code snippet.
    ///
    /// See the jsonnet language reference for details on what a top-level
    /// argument is. Specifically, see the section on [top-level arguments][0]
    ///
    /// [0]: https://jsonnet.org/ref/language.html#top-level-arguments-tlas
    ///
    /// # Panics
    /// This method panics if either of `key` or `value` contain a nul byte.
    pub fn tla_code(&mut self, key: &str, val: &str) {
        let key = str_to_cstring(key);
        let val = str_to_cstring(val);

        unsafe { sys::jsonnet_tla_code(self.as_raw(), key.as_ptr(), val.as_ptr()) }
    }

    /// Bind a jsonnet top-level argument to a provided json value.
    ///
    /// See the jsonnet language reference for details on what a top-level
    /// argument is. Specifically, see the section on [top-level arguments][0]
    ///
    /// [0]: https://jsonnet.org/ref/language.html#top-level-arguments-tlas
    ///
    /// # Errors
    /// This method will only return an error if the serialization of `value`
    /// returns an error.
    ///
    /// # Panics
    /// This method panics if either of `key` or the serialized JSON form of
    /// `value` contain a nul byte.
    #[cfg(feature = "json")]
    pub fn tla_json<V>(&mut self, key: &str, value: &V) -> serde_json::Result<()>
    where
        V: Serialize + ?Sized,
    {
        let json = serde_json::to_string(value)?;

        let mut code = String::with_capacity(json.len() + 32);
        code.push_str("std.parseJson(");
        jsonnet_escape(&json, &mut code)?;
        code.push(')');

        self.tla_code(key, &code);
        Ok(())
    }

    /// Add to the default import callback's library search path.
    ///
    /// The search order is last to first, so more recently appended paths take
    /// precedence.
    pub fn jpath_add(&mut self, jpath: &Path) {
        let jpath = osstr_to_cstring(jpath.as_os_str());

        unsafe { sys::jsonnet_jpath_add(self.as_raw(), jpath.as_ptr()) };
    }

    /// Evaluate some Jsonnet code.
    ///
    /// Depending on `options` this can either read the jsonnet from a file, or
    /// evaluate a jsonnet snippet.
    ///
    /// # Errors
    /// This function will return an error if:
    /// - the Jsonnet VM encounters an error while evaluating the program, or,
    /// - the resulting string is not valid UTF-8.
    pub fn evaluate(&mut self, options: EvaluateOptions<'_>) -> Result<String> {
        let output = self.evaluate_raw(options)?;

        match output.to_str() {
            Ok(mut output) => {
                // The output string from libjsonnet always includes an extra newline at the
                // end. This doesn't matter for json output but it corrupts the string when
                // doing string output.
                //
                // We strip it here ourselves to avoid that issue.
                if output.ends_with('\n') {
                    output = &output[..output.len() - 1];
                }

                Ok(output.to_owned())
            }
            Err(e) => Err(Error::utf8(e)),
        }
    }

    /// Evaluate some jsonnet code and parse the resulting json to a rust type.
    ///
    /// Depending on `options` this can either read the jsonnet from a file, or
    /// evaluate a jsonnet snippet. This function will ignore the
    /// [`string_output`] setting on `options`.
    ///
    /// # Errors
    /// This function will return an error if:
    /// - the Jsonnet VM encounters an error while evaluating the program, or,
    /// - the resulting JSON could not be parsed as a `T`.
    ///
    /// [`string_output`]: EvaluateOptions::string_output
    #[cfg(feature = "json")]
    pub fn evaluate_json<T>(&mut self, options: EvaluateOptions<'_>) -> Result<T>
    where
        T: DeserializeOwned,
    {
        let json = self.evaluate_raw(options.string_output(false))?;
        let bytes = json.to_bytes();
        serde_json::from_slice(bytes).map_err(|e| Error(ErrorImpl::Json(e)))
    }

    /// Evaluate Jsonnet code, returning a number of named JSON files.
    ///
    /// Depending on `options` this can either read the jsonnet from a file, or
    /// evaluate a jsonnet snippet.
    ///
    /// # Errors
    /// This function will return an error if the jsonnet VM encounters an error
    /// while evaluating the program.
    pub fn evaluate_multi(&mut self, options: EvaluateOptions<'_>) -> Result<MultiIter<'_>> {
        let filename = osstr_to_cstring(options.filename.as_os_str());
        let snippet = options.snippet.map(str_to_cstring);

        if options.string_output {
            self.string_output(true);
        }

        let mut error = 0;
        let output = if let Some(snippet) = snippet {
            unsafe {
                sys::jsonnet_evaluate_snippet_multi(
                    self.as_raw(),
                    filename.as_ptr(),
                    snippet.as_ptr(),
                    &mut error,
                )
            }
        } else {
            unsafe {
                sys::jsonnet_evaluate_file_multi(self.as_raw(), filename.as_ptr(), &mut error)
            }
        };

        if options.string_output {
            self.string_output(false);
        }

        if error == 0 {
            unsafe { Ok(MultiIter::new(self, output)) }
        } else {
            unsafe { Err(Error::native(&JsonnetString::from_raw(self, output))) }
        }
    }

    /// Evaluate Jsonnet code, returning a number of named JSON files.
    ///
    /// Depending on `options` this can either read the jsonnet from a file, or
    /// evaluate a jsonnet snippet.
    ///
    /// # Errors
    /// This function will return an error if the jsonnet VM encounters an error
    /// while evaluating the program.
    pub fn evaluate_stream(&mut self, options: EvaluateOptions<'_>) -> Result<StreamIter<'_>> {
        let filename = osstr_to_cstring(options.filename.as_os_str());
        let snippet = options.snippet.map(str_to_cstring);

        if options.string_output {
            self.string_output(true);
        }

        let mut error = 0;
        let output = if let Some(snippet) = snippet {
            unsafe {
                sys::jsonnet_evaluate_snippet_multi(
                    self.as_raw(),
                    filename.as_ptr(),
                    snippet.as_ptr(),
                    &mut error,
                )
            }
        } else {
            unsafe {
                sys::jsonnet_evaluate_file_multi(self.as_raw(), filename.as_ptr(), &mut error)
            }
        };

        if options.string_output {
            self.string_output(false);
        }

        if error == 0 {
            unsafe { Ok(StreamIter::new(self, output)) }
        } else {
            unsafe { Err(Error::native(&JsonnetString::from_raw(self, output))) }
        }
    }

    /// Evaluate some Jsonnet code and return the raw C string.
    ///
    /// This is useful for cases where the resulting string may not be valid
    /// UTF-8. You may also want to consider calling `evaluate_json` to convert
    /// the resulting output directly to a JSON object.
    ///
    /// Depending on `options` this can either read the jsonnet from a file, or
    /// evaluate a jsonnet snippet.
    ///
    /// # Errors
    /// This function will return an error if the Jsonnet VM encounters an error
    /// while attempting to run the program.
    pub fn evaluate_raw<'a>(
        &'a mut self,
        options: EvaluateOptions<'_>,
    ) -> Result<JsonnetString<'a>> {
        let filename = osstr_to_cstring(options.filename.as_os_str());
        let snippet = options.snippet.map(str_to_cstring);

        if options.string_output {
            self.string_output(true);
        }

        let mut error = 0;
        let output = if let Some(snippet) = snippet {
            unsafe {
                sys::jsonnet_evaluate_snippet(
                    self.as_raw(),
                    filename.as_ptr(),
                    snippet.as_ptr(),
                    &mut error,
                )
            }
        } else {
            unsafe { sys::jsonnet_evaluate_file(self.as_raw(), filename.as_ptr(), &mut error) }
        };

        if options.string_output {
            self.string_output(false);
        }

        let output = unsafe { JsonnetString::from_raw(self, output) };

        if error == 0 {
            Ok(output)
        } else {
            Err(Error::native(&output))
        }
    }

    /// Evaluate a file containing Jsonnet code.
    ///
    /// # Errors
    /// This function will return an error if:
    /// - the Jsonnet VM encounters an error while evaluating the program, or,
    /// - the resulting string is not valid UTF-8.
    pub fn evaluate_file(&mut self, filename: impl AsRef<Path>) -> Result<String> {
        self.evaluate(EvaluateOptions::new(filename.as_ref()))
    }

    /// Evaluate a Jsonnet snippet.
    ///
    /// The filename provided is used for diagnostics and for resolving imports
    /// within the jsonnet code.
    ///
    /// # Errors
    /// This function will return an error if:
    /// - the Jsonnet VM encounters an error while evaluating the program, or,
    /// - the resulting string is not valid UTF-8.
    pub fn evaluate_snippet(
        &mut self,
        filename: impl AsRef<Path>,
        snippet: &str,
    ) -> Result<String> {
        self.evaluate(EvaluateOptions::new(filename.as_ref()).snippet(snippet))
    }
}

impl Drop for JsonnetVm {
    fn drop(&mut self) {
        unsafe { sys::jsonnet_destroy(self.as_raw()) }
    }
}

impl Default for JsonnetVm {
    fn default() -> Self {
        Self::new()
    }
}

/// Options that control details of how jsonnet code is evaluated.
#[derive(Copy, Clone, Debug)]
pub struct EvaluateOptions<'a> {
    filename: &'a Path,
    snippet: Option<&'a str>,
    string_output: bool,
}

impl<'a> EvaluateOptions<'a> {
    /// Create a new set of options for the provided file path.
    pub fn new<P>(filename: &'a P) -> Self
    where
        P: AsRef<Path> + ?Sized,
    {
        Self {
            filename: filename.as_ref(),
            snippet: None,
            string_output: false,
        }
    }

    /// Execute the provided jsonnet snippet instead of loading code from the
    /// filename.
    ///
    /// The filename will still be used for resolving imports and within error
    /// messages.
    pub fn snippet(mut self, snippet: &'a str) -> Self {
        self.snippet = Some(snippet);
        self
    }

    /// If the result of the jsonnet program is a string, then it should be
    /// returned directly without being json-encoded.
    ///
    /// Generally this isn't what you want, since there is no way to tell that
    /// the jsonnet program actually returned a string instead of encoded json.
    pub fn string_output(mut self, value: bool) -> Self {
        self.string_output = value;
        self
    }
}

/// Iterator over the values returned by [`JsonnetVm::evaluate_multi`].
///
/// The [`Iterator`] impl for this type returns owned strings, but you can use
/// [`next_lending`] or [`next_raw`] to get at the values without needing to
/// copy them.
///
/// [`next_lending`]: MultiIter::next_lending
/// [`next_raw`]: MultiIter::next_raw
pub struct MultiIter<'a> {
    vm: &'a JsonnetVm,
    buf: NonNull<c_char>,
    off: *const c_char,
}

impl<'a> MultiIter<'a> {
    /// Create a MultiIter from a buffer.
    ///
    /// # Safety
    /// `buf` must be a pointer returned from a call to a
    /// `jsonnet_evaluate_*_multi` function.
    unsafe fn new(vm: &'a JsonnetVm, buf: *mut c_char) -> Self {
        Self {
            vm,
            buf: unsafe { NonNull::new_unchecked(buf) },
            off: buf,
        }
    }

    /// Get the next entry in the returned list.
    pub fn next_raw(&mut self) -> Option<(&CStr, &CStr)> {
        let key = unsafe { CStr::from_ptr(self.off) };

        // the return from the jsonnet_evaluate_*_multi methods specifies that the list
        // ends when we encounter `\0\0`. This translates to running into an empty key.
        if key.is_empty() {
            return None;
        }

        let val = unsafe { CStr::from_ptr(self.off.add(key.count_bytes() + 1)) };
        self.off = unsafe { val.as_ptr().add(val.count_bytes() + 1) };

        Some((key, val))
    }

    /// Get the next entry in the returned list as strings.
    ///
    /// # Panics
    /// Panics if either the key or the value contains invalid UTF-8.
    pub fn next_lending(&mut self) -> Option<(&str, &str)> {
        let (key, val) = self.next_raw()?;

        let key = key
            .to_str()
            .expect("returned string contained invalid UTF8");
        let val = val
            .to_str()
            .expect("returned string contained invalid UTF8");

        Some((key, val))
    }
}

impl<'a> Iterator for MultiIter<'a> {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        let (key, val) = self.next_lending()?;

        Some((key.to_owned(), val.to_owned()))
    }
}

impl<'a> FusedIterator for MultiIter<'a> {}

impl<'a> Drop for MultiIter<'a> {
    fn drop(&mut self) {
        unsafe { sys::jsonnet_realloc(self.vm.as_raw(), self.buf.as_ptr(), 0) };
    }
}

/// Iterator over the values returned by [`JsonnetVm::evaluate_stream`].
///
/// The [`Iterator`] impl for this type returns owned strings, but you can use
/// [`next_lending`] or [`next_raw`] to get at the values without needing to
/// copy them.
///
/// [`next_lending`]: StreamIter::next_lending
/// [`next_raw`]: StreamIter::next_raw
pub struct StreamIter<'a> {
    vm: &'a JsonnetVm,
    buf: NonNull<c_char>,
    off: *const c_char,
}

impl<'a> StreamIter<'a> {
    /// Create a StreamIter from a buffer.
    ///
    /// # Safety
    /// `buf` must be a pointer returned from a call to a
    /// `jsonnet_evaluate_*_stream` function.
    unsafe fn new(vm: &'a JsonnetVm, buf: *mut c_char) -> Self {
        Self {
            vm,
            buf: unsafe { NonNull::new_unchecked(buf) },
            off: buf,
        }
    }

    /// Get the next entry in the returned list.
    pub fn next_raw(&mut self) -> Option<&CStr> {
        let key = unsafe { CStr::from_ptr(self.off) };
        if key.is_empty() {
            return None;
        }

        self.off = unsafe { self.off.add(key.count_bytes() + 1) };
        Some(key)
    }

    /// Get the next entry in the returned list as a string.
    ///
    /// # Panics
    /// Panics if either the key or the value contains invalid UTF-8.
    pub fn next_lending(&mut self) -> Option<&str> {
        Some(
            self.next_raw()?
                .to_str()
                .expect("returned string contained invalid UTF8"),
        )
    }
}

impl<'a> Iterator for StreamIter<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_lending().map(|key| key.to_owned())
    }
}

impl<'a> Drop for StreamIter<'a> {
    fn drop(&mut self) {
        unsafe { sys::jsonnet_realloc(self.vm.as_raw(), self.buf.as_ptr(), 0) };
    }
}

/// Error type returned by methods within this crate.
#[derive(Debug)]
pub struct Error(ErrorImpl);

#[derive(Debug)]
enum ErrorImpl {
    /// A native error emitted directly from libjsonnet
    Vm(String),

    /// A string returned by libjsonnet did not contain valid UTF-8.
    InvalidUtf8(std::str::Utf8Error),

    /// An error emitted while serializing to a JsonValue.
    #[cfg_attr(not(feature = "serde"), allow(dead_code))]
    Serde(String),

    /// An error emitted when deserializing the resulting JSON to a rust type.
    #[cfg(feature = "json")]
    Json(serde_json::Error),
}

impl Error {
    fn native(s: &JsonnetString<'_>) -> Self {
        Self(ErrorImpl::Vm(s.to_string_lossy().into_owned()))
    }

    fn utf8(e: std::str::Utf8Error) -> Self {
        Self(ErrorImpl::InvalidUtf8(e))
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            ErrorImpl::Vm(error) => f.write_str(error),
            ErrorImpl::Serde(error) => f.write_str(error),
            ErrorImpl::InvalidUtf8(_) => f.write_str("returned string contained invalid UTF-8"),
            #[cfg(feature = "json")]
            ErrorImpl::Json(error) => write!(f, "failed to deserialize json: {error}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.0 {
            ErrorImpl::InvalidUtf8(e) => Some(e),
            #[cfg(feature = "json")]
            ErrorImpl::Json(e) => Some(e),
            _ => None,
        }
    }
}

#[cfg(unix)]
fn bytes_to_osstr(bytes: &[u8]) -> Result<&OsStr, Utf8Error> {
    use std::os::unix::ffi::OsStrExt;

    Ok(OsStr::from_bytes(bytes))
}

#[cfg(not(unix))]
fn bytes_to_osstr(bytes: &[u8]) -> Result<&OsStr, Utf8Error> {
    let path = std::str::from_utf8(bytes)?;
    Ok(OsStr::new(path))
}

fn str_to_cstring(s: &str) -> CString {
    let mut bytes = Vec::with_capacity(s.len() + 1);
    bytes.extend_from_slice(s.as_bytes());
    bytes.push(b'\0');

    CString::from_vec_with_nul(bytes).expect("string contained a nul byte")
}

fn osstr_to_cstring(s: &OsStr) -> CString {
    let mut bytes = Vec::with_capacity(s.len() + 1);
    bytes.extend_from_slice(s.as_encoded_bytes());
    bytes.push(b'\0');

    match CString::from_vec_with_nul(bytes) {
        Ok(s) => s,
        Err(e) => panic!("OsStr contained a nul byte: {e}"),
    }
}

/// Escape a string suitably for inserting it into a jsonnet string literal.
#[cfg(feature = "json")]
fn jsonnet_escape(mut input: &str, output: &mut String) -> serde_json::Result<()> {
    use ::serde::ser::Error;

    output.push('"');

    while let Some((index, b)) = input
        .bytes()
        .enumerate()
        .find(|(_, b)| matches!(b, b'\0' | b'\\' | b'"'))
    {
        let (head, rest) = input.split_at(index);
        output.push_str(head);

        input = &rest[1..];
        match b {
            b'\0' => {
                return Err(serde_json::Error::custom(
                    "serialized string contained a nul byte",
                ))
            }
            b'\\' => output.push_str("\\\\"),
            b'\"' => output.push_str("\\\""),
            _ => unreachable!(),
        }
    }

    output.push_str(input);
    output.push('"');
    Ok(())
}
