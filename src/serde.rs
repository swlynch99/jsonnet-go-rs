use std::borrow::Cow;

use jsonnet_go_sys as sys;
use serde::ser::{Error as _marker2, Impossible, SerializeMap};
use serde::{Serialize, Serializer};

use crate::{Error, JsonValue, JsonnetVm};

#[cfg_attr(docsrs, doc_cfg(feature = "serde"))]
pub fn to_json_value<'vm, T>(vm: &'vm JsonnetVm, value: &T) -> Result<JsonValue<'vm>, Error>
where
    T: Serialize,
{
    value.serialize(JsonValueSerializer::new(vm))
}

/// A serde serializer for [`JsonValue`]s.
#[cfg_attr(docsrs, doc_cfg(feature = "serde"))]
pub struct JsonValueSerializer<'vm> {
    vm: &'vm JsonnetVm,
}

impl<'vm> JsonValueSerializer<'vm> {
    pub fn new(vm: &'vm JsonnetVm) -> Self {
        Self { vm }
    }
}

impl<'vm> Serializer for JsonValueSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    type SerializeSeq = JsonSeqSerializer<'vm>;
    type SerializeTuple = JsonSeqSerializer<'vm>;
    type SerializeTupleStruct = JsonSeqSerializer<'vm>;
    type SerializeTupleVariant = VariantSerializer<'vm, JsonSeqSerializer<'vm>>;
    type SerializeMap = JsonMapSerializer<'vm>;
    type SerializeStruct = JsonMapSerializer<'vm>;
    type SerializeStructVariant = VariantSerializer<'vm, JsonMapSerializer<'vm>>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        Ok(JsonValue::bool(self.vm, v))
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v as f64)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v as f64)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v.into())
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        Ok(JsonValue::number(self.vm, v))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        let mut buf = [0u8; 4];
        self.serialize_str(v.encode_utf8(&mut buf))
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(JsonValue::string(self.vm, v))
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        <[u8]>::serialize(v, self)
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(JsonValue::null(self.vm))
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        self.serialize_str(variant)
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + serde::Serialize,
    {
        let value = value.serialize(Self::new(self.vm))?;
        let mut map = JsonMapSerializer::new(self.vm);
        map.insert(variant, value)?;
        map.end()
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(JsonSeqSerializer::new(self.vm))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(VariantSerializer::new(
            self.vm,
            self.serialize_seq(Some(len))?,
            variant,
        ))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(JsonMapSerializer::new(self.vm))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(VariantSerializer::new(
            self.vm,
            self.serialize_map(Some(len))?,
            variant,
        ))
    }
}

#[cfg_attr(docsrs, doc_cfg(feature = "serde"))]
pub struct JsonSeqSerializer<'vm> {
    vm: &'vm JsonnetVm,
    array: JsonValue<'vm>,
}

impl<'vm> JsonSeqSerializer<'vm> {
    pub fn new(vm: &'vm JsonnetVm) -> Self {
        let array = JsonValue::array(vm);

        Self { vm, array }
    }

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Error>
    where
        T: ?Sized + Serialize,
    {
        let value = value.serialize(JsonValueSerializer::new(self.vm))?;

        unsafe {
            sys::jsonnet_json_array_append(
                self.vm.as_raw(),
                self.array.as_raw_mut(),
                value.into_raw(),
            );
        }

        Ok(())
    }
}

impl<'vm> serde::ser::SerializeSeq for JsonSeqSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.serialize_element(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.array)
    }
}

impl<'vm> serde::ser::SerializeTuple for JsonSeqSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.serialize_element(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.array)
    }
}

impl<'vm> serde::ser::SerializeTupleStruct for JsonSeqSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.serialize_element(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.array)
    }
}

#[cfg_attr(docsrs, doc_cfg(feature = "serde"))]
pub struct JsonMapSerializer<'vm> {
    vm: &'vm JsonnetVm,
    map: JsonValue<'vm>,
    key: Option<Cow<'static, str>>,
}

impl<'vm> JsonMapSerializer<'vm> {
    pub fn new(vm: &'vm JsonnetVm) -> Self {
        let map = JsonValue::object(vm);

        Self { vm, map, key: None }
    }

    fn insert(&mut self, key: &str, value: JsonValue<'vm>) -> Result<(), Error> {
        if key.bytes().any(|b| b == b'\0') {
            return Err(Error::custom("map key contained a nul byte"));
        }

        self.map.insert(key, value);
        Ok(())
    }
}

impl<'vm> serde::ser::SerializeMap for JsonMapSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_key<T>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.key = Some(key.serialize(StringSerializer)?);
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let key = self.key.take().unwrap();
        let value = value.serialize(JsonValueSerializer::new(self.vm))?;

        self.insert(&key, value)?;
        Ok(())
    }

    fn serialize_entry<K, V>(&mut self, key: &K, value: &V) -> Result<(), Self::Error>
    where
        K: ?Sized + Serialize,
        V: ?Sized + Serialize,
    {
        let key = key.serialize(StringSerializer)?;
        let value = value.serialize(JsonValueSerializer::new(self.vm))?;

        self.insert(&key, value)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        assert!(
            self.key.is_none(),
            "end called with a key still waiting to be used"
        );

        Ok(self.map)
    }
}

impl<'vm> serde::ser::SerializeStruct for JsonMapSerializer<'vm> {
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        let value = value.serialize(JsonValueSerializer::new(self.vm))?;
        self.insert(key, value)?;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(self.map)
    }
}

impl serde::ser::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: std::fmt::Display,
    {
        Error(crate::ErrorImpl::Serde(msg.to_string()))
    }
}

#[doc(hidden)]
pub struct VariantSerializer<'vm, S> {
    vm: &'vm JsonnetVm,
    ser: S,
    variant: &'static str,
}

impl<'vm, S> VariantSerializer<'vm, S> {
    fn new(vm: &'vm JsonnetVm, ser: S, variant: &'static str) -> Self {
        Self { vm, ser, variant }
    }
}

impl<'vm, S> serde::ser::SerializeStructVariant for VariantSerializer<'vm, S>
where
    S: serde::ser::SerializeStruct<Ok = JsonValue<'vm>, Error = Error>,
{
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.ser.serialize_field(key, value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let value = self.ser.end()?;
        let mut ser = JsonMapSerializer::new(self.vm);
        ser.insert(self.variant, value)?;
        ser.end()
    }
}

impl<'vm, S> serde::ser::SerializeTupleVariant for VariantSerializer<'vm, S>
where
    S: serde::ser::SerializeTuple<Ok = JsonValue<'vm>, Error = Error>,
{
    type Ok = JsonValue<'vm>;
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        self.ser.serialize_element(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        let value = self.ser.end()?;
        let mut ser = JsonMapSerializer::new(self.vm);
        ser.insert(self.variant, value)?;
        ser.end()
    }
}

struct StringSerializer;

impl StringSerializer {
    fn error_not_string(&self, ty: impl std::fmt::Display) -> Error {
        Error::custom(format_args!(
            "cannot serialize {ty} as an object key, only strings are permitted"
        ))
    }
}

macro_rules! error_not_string {
    {
        $( $name:ident => $ty:ty; )*
    } => {
        $(
            fn $name(self, _: $ty) -> Result<Self::Ok, Self::Error> {
                Err(Error::custom(concat!(
                    "cannot serialize a ",
                    stringify!($ty),
                    " as an object key, only strings are permitted",
                )))
            }
        )*
    }
}

impl Serializer for StringSerializer {
    type Ok = Cow<'static, str>;
    type Error = Error;

    type SerializeSeq = Impossible<Self::Ok, Self::Error>;
    type SerializeTuple = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleStruct = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleVariant = Impossible<Self::Ok, Self::Error>;
    type SerializeMap = Impossible<Self::Ok, Self::Error>;
    type SerializeStruct = Impossible<Self::Ok, Self::Error>;
    type SerializeStructVariant = Impossible<Self::Ok, Self::Error>;

    error_not_string! {
        serialize_bool => bool;
        serialize_i8 => i8;
        serialize_i16 => i16;
        serialize_i32 => i32;
        serialize_i64 => i64;
        serialize_u8 => u8;
        serialize_u16 => u16;
        serialize_u32 => u32;
        serialize_u64 => u64;
        serialize_f32 => f32;
        serialize_f64 => f64;
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        let mut buf = [0u8; 4];
        self.serialize_str(v.encode_utf8(&mut buf))
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(v.to_owned().into())
    }

    fn serialize_bytes(self, _: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err(self.error_not_string("bytes"))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(self.error_not_string("none"))
    }

    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(self.error_not_string("null"))
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(name.into())
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(variant.into())
    }

    fn serialize_newtype_struct<T>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T>(
        self,
        name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        Err(self.error_not_string(format_args!("newtype variant `{name}`")))
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(self.error_not_string("a sequence"))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(self.error_not_string("a tuple"))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(self.error_not_string("a tuple struct"))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err(self.error_not_string("a tuple variant"))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err(self.error_not_string("a tuple variant"))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err(self.error_not_string("a struct"))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err(self.error_not_string("a struct variant"))
    }
}
