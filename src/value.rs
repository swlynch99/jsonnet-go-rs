use std::ffi::CStr;
use std::fmt;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

use jsonnet_go_sys::{self as sys};

use crate::JsonnetVm;

/// A borrowed jsonnet JSON value.
///
/// These are used as part of the native function API.
#[derive(Copy, Clone)]
pub struct JsonVal<'vm: 'value, 'value> {
    vm: NonNull<sys::JsonnetVm>,
    value: NonNull<sys::JsonnetJsonValue>,
    _marker1: PhantomData<&'vm sys::JsonnetVm>,
    _marker2: PhantomData<&'value sys::JsonnetJsonValue>,
}

impl<'vm: 'value, 'value> JsonVal<'vm, 'value> {
    /// Create a new `JsonVal` from its components.
    pub fn new(vm: &'vm JsonnetVm, value: &'value sys::JsonnetJsonValue) -> Self {
        Self {
            vm: vm.vm,
            value: NonNull::from(value),
            _marker1: PhantomData,
            _marker2: PhantomData,
        }
    }

    /// Get a pointer to the underlying [`sys::JsonnetJsonValue`].
    pub fn as_raw(&self) -> *const sys::JsonnetJsonValue {
        self.value.as_ptr()
    }

    /// Returns whether this value is null.
    pub fn is_null(&self) -> bool {
        unsafe { sys::jsonnet_json_extract_null(self.vm.as_ptr(), self.value.as_ptr()) != 0 }
    }

    /// If this value is a boolean, then returns its value.
    pub fn as_bool(&self) -> Option<bool> {
        match unsafe { sys::jsonnet_json_extract_bool(self.vm.as_ptr(), self.value.as_ptr()) } {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    /// If this value is a number, then returns its value.
    pub fn as_number(&self) -> Option<f64> {
        let mut value = 0.0;
        match unsafe {
            sys::jsonnet_json_extract_number(self.vm.as_ptr(), self.value.as_ptr(), &mut value)
        } {
            1 => Some(value),
            _ => None,
        }
    }

    /// If this value is a string, then returns its value.
    pub fn as_string(&self) -> Option<&'value str> {
        let value =
            unsafe { sys::jsonnet_json_extract_string(self.vm.as_ptr(), self.value.as_ptr()) };
        if value.is_null() {
            return None;
        }

        let cstr = unsafe { CStr::from_ptr(value) };
        match cstr.to_str() {
            Ok(str) => Some(str),

            // The API contract guarantees that the string is valid UTF-8.
            Err(_) => unreachable!("jsonnet json value contained a non-utf-8 string"),
        }
    }
}

impl<'vm, 'value> fmt::Debug for JsonVal<'vm, 'value> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_null() {
            f.write_str("Null")
        } else if let Some(bool) = self.as_bool() {
            f.debug_tuple("Bool").field(&bool).finish()
        } else if let Some(number) = self.as_number() {
            f.debug_tuple("Number").field(&number).finish()
        } else if let Some(string) = self.as_string() {
            f.debug_tuple("String").field(&string).finish()
        } else {
            f.write_str("<opaque>")
        }
    }
}

/// An owned jsonnet JSON value.
///
/// This can contain any jsonnet value. However, libjsonnet only provides access
/// to a limited subset of the available types. It is possible to extract the
/// value if it is null, a boolean, a string, or a number. It is not possible to
/// otherwise inspect the inner value of the `JsonValue`.
///
/// Creating new `JsonValue`s however, is less restricted. Any valid JSON object
/// can be built. With the `serde` feature enabled, you can use the [`serde`][0]
/// module to serialize a rust struct directly to a `JsonValue`.
///
/// [0]: crate::serde
pub struct JsonValue<'vm> {
    vm: NonNull<sys::JsonnetVm>,
    value: NonNull<sys::JsonnetJsonValue>,
    _marker: PhantomData<&'vm sys::JsonnetVm>,
}

impl<'vm> JsonValue<'vm> {
    /// Create a new JsonValue from its raw parts.
    ///
    /// # Safety
    /// `value` must be a pointer returned from one of the `jsonnet_json_make_*`
    /// libjsonnet functions.
    pub unsafe fn from_parts(vm: &'vm JsonnetVm, value: *mut sys::JsonnetJsonValue) -> Self {
        Self {
            vm: vm.vm,
            value: unsafe { NonNull::new_unchecked(value) },
            _marker: PhantomData,
        }
    }

    /// Get a pointer to the underlying [`sys::JsonnetJsonValue`].
    pub fn as_raw(&self) -> *const sys::JsonnetJsonValue {
        self.value.as_ptr()
    }

    /// Get a mutable pointer to the underlying [`sys::JsonnetJsonValue`].
    pub fn as_raw_mut(&mut self) -> *mut sys::JsonnetJsonValue {
        self.value.as_ptr()
    }

    /// Convert this [`JsonValue`] into a raw [`sys::JsonnetJsonValue`] pointer.
    pub fn into_raw(self) -> *mut sys::JsonnetJsonValue {
        ManuallyDrop::new(self).value.as_ptr()
    }

    /// Get a [`JsonVal`] reference to this value.
    pub fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value> {
        JsonVal {
            vm: self.vm,
            value: self.value,
            _marker1: PhantomData,
            _marker2: PhantomData,
        }
    }

    /// Returns whether this value is null.
    pub fn is_null(&self) -> bool {
        self.as_json_val().is_null()
    }

    /// If this value is a boolean, then returns its value.
    pub fn as_bool(&self) -> Option<bool> {
        self.as_json_val().as_bool()
    }

    /// If this value is a number, then returns its value.
    pub fn as_number(&self) -> Option<f64> {
        self.as_json_val().as_number()
    }

    /// If this value is a string, then returns its value.
    pub fn as_string(&self) -> Option<&str> {
        self.as_json_val().as_string()
    }

    /// Create a `JsonValue` representing null.
    pub fn null(vm: &'vm JsonnetVm) -> Self {
        let value = unsafe { sys::jsonnet_json_make_null(vm.as_raw()) };

        // SAFETY: value was returned from jsonnet_json_make_null
        unsafe { Self::from_parts(vm, value) }
    }

    /// Create a `JsonValue` representing a boolean.
    pub fn bool(vm: &'vm JsonnetVm, value: bool) -> Self {
        let value = unsafe { sys::jsonnet_json_make_bool(vm.as_raw(), value.into()) };

        // SAFETY: value was returned from jsonnet_json_make_bool
        unsafe { Self::from_parts(vm, value) }
    }

    /// Create a `JsonValue` representing a string.
    pub fn string(vm: &'vm JsonnetVm, value: &str) -> Self {
        let cstr = crate::str_to_cstring(value);
        let value = unsafe { sys::jsonnet_json_make_string(vm.as_raw(), cstr.as_ptr()) };

        // SAFETY: value was returned from jsonnet_json_make_string
        unsafe { Self::from_parts(vm, value) }
    }

    /// Create a `JsonValue` representing a number.
    pub fn number(vm: &'vm JsonnetVm, value: f64) -> Self {
        let value = unsafe { sys::jsonnet_json_make_number(vm.as_raw(), value) };

        // SAFETY: value was returned from jsonnet_json_make_number
        unsafe { Self::from_parts(vm, value) }
    }

    /// Create a `JsonValue` representing an empty array.
    pub fn array(vm: &'vm JsonnetVm) -> Self {
        let value = unsafe { sys::jsonnet_json_make_array(vm.as_raw()) };
        unsafe { Self::from_parts(vm, value) }
    }

    /// Create a `JsonValue` representing an object.
    pub fn object(vm: &'vm JsonnetVm) -> Self {
        let value = unsafe { sys::jsonnet_json_make_object(vm.as_raw()) };
        unsafe { Self::from_parts(vm, value) }
    }

    /// Append an object to this array value.
    ///
    /// If this value is not currently an array, then its value will be
    /// replaced with an empty array before appending to it.
    pub fn append(&mut self, value: impl AsJsonVal<'vm>) {
        let val = value.as_json_val();

        assert!(
            val.vm.as_ptr() == self.vm.as_ptr(),
            "attempted to insert a JsonValue from a different Jsonnet VM"
        );

        unsafe {
            sys::jsonnet_json_array_append(
                self.vm.as_ptr(),
                self.as_raw_mut(),
                val.as_raw() as *mut _,
            );
        }
    }

    /// Set a field within this object value.
    ///
    /// If this value is not currently an object then its value will be replaced
    /// with an empty object before inserting the new field.
    pub fn insert(&mut self, key: &str, value: impl AsJsonVal<'vm>) {
        let key = crate::str_to_cstring(key);
        let val = value.as_json_val();

        assert!(
            val.vm.as_ptr() == self.vm.as_ptr(),
            "attempted to insert a JsonValue from a different Jsonnet VM"
        );

        unsafe {
            sys::jsonnet_json_object_append(
                self.vm.as_ptr(),
                self.as_raw_mut(),
                key.as_ptr(),
                val.as_raw() as *mut _,
            );
        }
    }
}

impl<'vm> Drop for JsonValue<'vm> {
    fn drop(&mut self) {
        unsafe { sys::jsonnet_json_destroy(self.vm.as_ptr(), self.value.as_ptr()) }
    }
}

impl<'vm> fmt::Debug for JsonValue<'vm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_json_val().fmt(f)
    }
}

/// Trait for types which can be converted to a [`JsonVal`].
pub trait AsJsonVal<'vm> {
    /// Get a [`JsonVal`] reference to `self`.
    fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value>;
}

impl<'vm> AsJsonVal<'vm> for JsonValue<'vm> {
    fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value> {
        self.as_json_val()
    }
}

impl<'vm, 'val1> AsJsonVal<'vm> for JsonVal<'vm, 'val1> {
    fn as_json_val<'val2>(&'val2 self) -> JsonVal<'vm, 'val2> {
        *self
    }
}

impl<'vm, 'a, T> AsJsonVal<'vm> for &'a T
where
    T: AsJsonVal<'vm>,
{
    fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value> {
        (*self).as_json_val()
    }
}

impl<'vm, 'a, T> AsJsonVal<'vm> for &'a mut T
where
    T: AsJsonVal<'vm>,
{
    fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value> {
        (**self).as_json_val()
    }
}
