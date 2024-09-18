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
//! # use jsonnet_go::{JsonnetVm, Result};
//! #
//! # fn main() -> Result<()> {
//! let jsonnet = "{ field: std.base64('Hello, World!') }";
//! let mut vm = JsonnetVm::new();
//!
//! let json = vm.evaluate_snippet("test.jsonnet", jsonnet)?;
//! # Ok(())
//! # }
//! ```
//!
//! [`evaluate_file`]: JsonnetVm::evaluate_file
//! [`evaluate_snippet`]: JsonnetVm::evaluate_snippet

#![cfg_attr(docsrs, feature(doc_cfg))]

use std::collections::BTreeMap;
use std::ffi::{c_char, c_int, c_void, CStr, CString, OsStr};
use std::fmt;
use std::iter::FusedIterator;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::ptr::NonNull;
use std::str::Utf8Error;

use jsonnet_go_sys as sys;

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc_cfg(feature = "serde"))]
pub mod serde;
mod value;

pub use crate::value::{AsJsonVal, JsonVal, JsonValue};

pub type Result<T, E = Error> = std::result::Result<T, E>;

pub struct JsonnetVm {
    vm: NonNull<sys::JsonnetVm>,

    // Callback data for the import callback.
    //
    // This ensures that we can drop it when we are dropped or when a new import callback is
    // raised.
    import_cb_data: Box<dyn Send>,

    native_cb_data: BTreeMap<CString, Box<dyn Send>>,
}

impl JsonnetVm {
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
    pub fn native_callback<F, E>(
        &mut self,
        name: &str,
        params: impl Iterator<Item: AsRef<str>>,
        cb: F,
    ) where
        F: for<'vm> Fn(&'vm JsonnetVm, &[JsonVal<'vm, 'vm>]) -> Result<JsonValue<'vm>, E>,
        F: Send + Sync + 'static,
        E: fmt::Display,
    {
        struct NativeContext<F> {
            vm: NonNull<sys::JsonnetVm>,
            cb: F,
        }

        unsafe impl<F: Send> Send for NativeContext<F> {}

        extern "C" fn callback<F, E>(
            ctx: *mut c_void,
            argv: *const *const sys::JsonnetJsonValue,
            success: *mut c_int,
        ) -> *mut sys::JsonnetJsonValue
        where
            F: for<'vm> Fn(&'vm JsonnetVm, &[JsonVal<'vm, 'vm>]) -> Result<JsonValue<'vm>, E>,
            E: fmt::Display,
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
                        values.push(JsonVal::from_parts(&vm, *current));
                        current = current.add(1);
                    }
                }

                match (ctx.cb)(&vm, &values) {
                    Ok(value) => {
                        unsafe { *success = 0 };
                        value
                    }
                    Err(e) => {
                        unsafe { *success = 1 };
                        JsonValue::string(&vm, &e.to_string())
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

                    unsafe { *success = 1 };
                    message.into_raw()
                }
            }
        }

        let mut ctx = Box::new(NativeContext { vm: self.vm, cb });

        let name = str_to_cstring(name);
        let params: Vec<_> = params.map(|p| str_to_cstring(p.as_ref())).collect();
        let params: Vec<_> = params
            .iter()
            .map(|p| p.as_ptr())
            .chain(std::iter::once(std::ptr::null()))
            .collect();

        unsafe {
            sys::jsonnet_native_callback(
                self.as_raw(),
                name.as_ptr(),
                Some(callback::<F, E>),
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
    pub fn ext_code(&mut self, key: &str, val: &str) {
        let key = str_to_cstring(key);
        let val = str_to_cstring(val);

        unsafe { sys::jsonnet_ext_code(self.as_raw(), key.as_ptr(), val.as_ptr()) }
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

        unsafe { sys::jsonnet_tla_var(self.as_raw(), key.as_ptr(), val.as_ptr()) }
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
            Ok(output) => Ok(output.to_owned()),
            Err(e) => Err(Error::utf8(e)),
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
    pub fn new(filename: &'a Path) -> Self {
        Self {
            filename,
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

/// A C string whose memory is managed by the Jsonnet VM.
pub struct JsonnetString<'a> {
    vm: &'a JsonnetVm,
    ptr: NonNull<c_char>,
    len: usize,
}

impl<'a> JsonnetString<'a> {
    fn from_bytes(vm: &'a JsonnetVm, bytes: &[u8]) -> Self {
        assert!(
            bytes.iter().copied().any(|b| b == b'\0'),
            "cannot create a JsonnetString from a string with a nul byte"
        );

        unsafe {
            let mem = sys::jsonnet_realloc(vm.as_raw(), std::ptr::null_mut(), bytes.len() + 1);
            std::ptr::copy_nonoverlapping(bytes.as_ptr() as *const c_char, mem, bytes.len());
            std::ptr::write(mem.add(bytes.len() + 1), b'\0' as c_char);

            Self {
                vm,
                len: bytes.len(),
                ptr: NonNull::new_unchecked(mem),
            }
        }
    }

    fn from_str(vm: &'a JsonnetVm, str: &str) -> Self {
        Self::from_bytes(vm, str.as_bytes())
    }

    unsafe fn from_raw(vm: &'a JsonnetVm, ptr: *mut c_char) -> Self {
        let len = unsafe { CStr::from_ptr(ptr).count_bytes() + 1 };

        Self {
            vm,
            len,
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    fn into_raw(self) -> *mut c_char {
        let this = ManuallyDrop::new(self);
        this.ptr.as_ptr()
    }

    pub fn capacity(&self) -> usize {
        self.len + 1
    }
}

impl<'a> Drop for JsonnetString<'a> {
    fn drop(&mut self) {
        unsafe {
            sys::jsonnet_realloc(self.vm.as_raw(), self.ptr.as_ptr(), 0);
        }
    }
}

impl<'a> Deref for JsonnetString<'a> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        let bytes =
            unsafe { std::slice::from_raw_parts(self.ptr.as_ptr() as *const u8, self.capacity()) };
        unsafe { CStr::from_bytes_with_nul_unchecked(bytes) }
    }
}

pub(crate) struct JsonnetStringBuilder<'vm> {
    vm: &'vm JsonnetVm,
    ptr: NonNull<c_char>,
    len: usize,
    cap: usize,
}

impl<'vm> JsonnetStringBuilder<'vm> {
    pub fn with_capacity(vm: &'vm JsonnetVm, capacity: usize) -> Self {
        let cap = capacity + 1;
        let buf = unsafe { sys::jsonnet_realloc(vm.as_raw(), std::ptr::null_mut(), cap) };

        unsafe { *buf = b'\0' as c_char };

        Self {
            vm,
            ptr: unsafe { NonNull::new_unchecked(buf) },
            len: 0,
            cap,
        }
    }

    pub fn into_string(self) -> JsonnetString<'vm> {
        let this = ManuallyDrop::new(self);

        JsonnetString {
            vm: this.vm,
            ptr: this.ptr,
            len: this.len,
        }
    }

    fn push_str(&mut self, str: &str) {
        if self.cap < self.len + str.len() + 1 {
            let ncap = (self.cap * 2).max(self.len + str.len() + 1);
            let nbuf = unsafe { sys::jsonnet_realloc(self.vm.as_raw(), self.ptr.as_ptr(), ncap) };

            self.ptr = unsafe { NonNull::new_unchecked(nbuf) };
            self.cap = ncap;
        }

        unsafe {
            std::ptr::copy_nonoverlapping(
                str.as_ptr() as *const c_char,
                self.ptr.as_ptr().add(self.len),
                str.len(),
            );
        }

        self.len += str.len();

        unsafe { *self.ptr.as_ptr().add(self.len) = b'\0' as c_char };
    }
}

impl<'vm> fmt::Write for JsonnetStringBuilder<'vm> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }
}

#[derive(Debug)]
pub struct Error(ErrorImpl);

#[derive(Debug)]
enum ErrorImpl {
    /// A native error emitted directly from libjsonnet
    Vm(String),

    /// A string returned by libjsonnet did not contain valid UTF-8.
    InvalidUtf8(std::str::Utf8Error),
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
            ErrorImpl::InvalidUtf8(_) => f.write_str("returned string contained invalid UTF-8"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.0 {
            ErrorImpl::InvalidUtf8(e) => Some(e),
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
