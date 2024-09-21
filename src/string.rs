use std::ffi::{c_char, CStr};
use std::fmt;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::ptr::NonNull;

use jsonnet_go_sys as sys;

use crate::JsonnetVm;

/// A C string whose memory is managed by the Jsonnet VM.
pub struct JsonnetString<'a> {
    vm: &'a JsonnetVm,
    ptr: NonNull<c_char>,
    len: usize,
}

impl<'a> JsonnetString<'a> {
    pub(crate) fn from_bytes(vm: &'a JsonnetVm, bytes: &[u8]) -> Self {
        assert!(
            !bytes.iter().copied().any(|b| b == b'\0'),
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

    pub(crate) fn from_str(vm: &'a JsonnetVm, str: &str) -> Self {
        Self::from_bytes(vm, str.as_bytes())
    }

    pub(crate) unsafe fn from_raw(vm: &'a JsonnetVm, ptr: *mut c_char) -> Self {
        let len = unsafe { CStr::from_ptr(ptr).count_bytes() };

        Self {
            vm,
            len,
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    pub(crate) fn into_raw(self) -> *mut c_char {
        let this = ManuallyDrop::new(self);
        this.ptr.as_ptr()
    }

    pub(crate) fn capacity(&self) -> usize {
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

    pub fn push_str(&mut self, str: &str) {
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
