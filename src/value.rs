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
    pub fn new(vm: &'vm JsonnetVm, value: &'value sys::JsonnetJsonValue) -> Self {
        unsafe { Self::from_parts(vm, value) }
    }

    pub unsafe fn from_parts(vm: &'vm JsonnetVm, value: *const sys::JsonnetJsonValue) -> Self {
        Self {
            vm: vm.vm,
            value: unsafe { NonNull::new_unchecked(value as *mut _) },
            _marker1: PhantomData,
            _marker2: PhantomData,
        }
    }

    pub fn as_raw(&self) -> *const sys::JsonnetJsonValue {
        self.value.as_ptr()
    }

    pub fn is_null(&self) -> bool {
        unsafe { sys::jsonnet_json_extract_null(self.vm.as_ptr(), self.value.as_ptr()) != 0 }
    }

    pub fn as_bool(&self) -> Option<bool> {
        match unsafe { sys::jsonnet_json_extract_bool(self.vm.as_ptr(), self.value.as_ptr()) } {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }

    pub fn as_number(&self) -> Option<f64> {
        let mut value = 0.0;
        match unsafe {
            sys::jsonnet_json_extract_number(self.vm.as_ptr(), self.value.as_ptr(), &mut value)
        } {
            1 => Some(value),
            _ => None,
        }
    }

    pub fn as_string(&self) -> Option<&str> {
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
pub struct JsonValue<'vm>(JsonVal<'vm, 'vm>);

impl<'vm> JsonValue<'vm> {
    /// Create a new JsonValue from its raw parts.
    ///
    /// # Safety
    /// `value` must be a pointer returned from one of the `jsonnet_json_make_*`
    /// libjsonnet functions.
    pub unsafe fn from_parts(vm: &'vm JsonnetVm, value: *mut sys::JsonnetJsonValue) -> Self {
        Self(JsonVal::new(vm, &*value))
    }

    pub fn as_raw(&self) -> *const sys::JsonnetJsonValue {
        self.0.as_raw()
    }

    pub fn as_raw_mut(&mut self) -> *mut sys::JsonnetJsonValue {
        self.0.value.as_ptr()
    }

    pub fn into_raw(self) -> *mut sys::JsonnetJsonValue {
        ManuallyDrop::new(self).0.value.as_ptr()
    }

    pub fn as_json_val<'value>(&'value self) -> JsonVal<'vm, 'value> {
        self.0
    }

    pub fn is_null(&self) -> bool {
        self.0.is_null()
    }

    pub fn as_bool(&self) -> Option<bool> {
        self.0.as_bool()
    }

    pub fn as_number(&self) -> Option<f64> {
        self.0.as_number()
    }

    pub fn as_string(&self) -> Option<&str> {
        self.0.as_string()
    }

    /// Create a `JsonValue` representing null.
    pub fn null(vm: &'vm JsonnetVm) -> Self {
        let value = unsafe { sys::jsonnet_json_make_null(vm.as_raw()) };

        // SAFETY: value was returned from jsonnet_json_make_null
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

    /// Create a `JsonValue` representing an array.
    pub fn array<I, V>(vm: &'vm JsonnetVm, items: I) -> Self
    where
        I: IntoIterator<Item = V>,
        V: AsJsonVal<'vm>,
    {
        let value = unsafe { sys::jsonnet_json_make_array(vm.as_raw()) };
        let mut array = unsafe { Self::from_parts(vm, value) };

        for item in items {
            let val = item.as_json_val();

            assert!(
                val.vm.as_ptr() == vm.as_raw(),
                "attempted to insert a JsonValue from a different Jsonnet VM"
            );

            unsafe {
                sys::jsonnet_json_array_append(
                    vm.as_raw(),
                    array.as_raw_mut(),
                    val.as_raw() as *mut _,
                )
            };
        }

        array
    }

    /// Create a `JsonValue` representing an object.
    pub fn object<I, K, V>(vm: &'vm JsonnetVm, entries: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: AsRef<str>,
        V: AsJsonVal<'vm>,
    {
        let value = unsafe { sys::jsonnet_json_make_object(vm.as_raw()) };
        let mut object = unsafe { Self::from_parts(vm, value) };

        for (key, val) in entries {
            let key = crate::str_to_cstring(key.as_ref());
            let val = val.as_json_val();

            assert!(
                val.vm.as_ptr() == vm.as_raw(),
                "attempted to insert a JsonValue from a different Jsonnet VM"
            );

            unsafe {
                sys::jsonnet_json_object_append(
                    vm.as_raw(),
                    object.as_raw_mut(),
                    key.as_ptr(),
                    val.as_raw() as *mut _,
                );
            }
        }

        object
    }
}

impl<'vm> Drop for JsonValue<'vm> {
    fn drop(&mut self) {
        unsafe { sys::jsonnet_json_destroy(self.0.vm.as_ptr(), self.0.value.as_ptr()) }
    }
}

impl<'vm> fmt::Debug for JsonValue<'vm> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

pub trait AsJsonVal<'vm> {
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
