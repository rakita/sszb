//! Provides encoding (serialization) and decoding (deserialization) in the SimpleSerialize (SSZ)
//! format designed for use in Ethereum 2.0.
//!
//! Adheres to the Ethereum 2.0 but endian is switched [SSZ
//! specification](https://github.com/ethereum/eth2.0-specs/blob/v0.12.1/ssz/simple-serialize.md)
//! at v0.12.1.
//!
//! ## Example
//!
//! ```rust
//! use sszb_derive::{Encode, Decode};
//! use sszb::{Decode, Encode};
//!
//! #[derive(PartialEq, Debug, Encode, Decode)]
//! struct Foo {
//!     a: u64,
//!     b: Vec<u16>,
//! }
//!
//! fn sszb_encode_decode_example() {
//!     let foo = Foo {
//!         a: 42,
//!         b: vec![1, 3, 3, 7]
//!     };
//!
//!     let sszb_bytes: Vec<u8> = foo.as_sszb_bytes();
//!
//!     let decoded_foo = Foo::from_sszb_bytes(&sszb_bytes).unwrap();
//!
//!     assert_eq!(foo, decoded_foo);
//! }
//!
//! ```
//!
//! See `examples/` for manual implementations of the `Encode` and `Decode` traits.

mod decode;
mod encode;
mod union_selector;

pub use decode::{
    impls::decode_list_of_variable_length_items, read_offset, split_union_bytes, Decode,
    DecodeError, SszDecoder, SszDecoderBuilder,
};
pub use encode::{encode_length, Encode, SszEncoder};
pub use union_selector::UnionSelector;

/// The number of bytes used to represent an offset.
pub const BYTES_PER_LENGTH_OFFSET: usize = 4;
/// The maximum value that can be represented using `BYTES_PER_LENGTH_OFFSET`.
#[cfg(target_pointer_width = "32")]
pub const MAX_LENGTH_VALUE: usize = (std::u32::MAX >> (8 * (4 - BYTES_PER_LENGTH_OFFSET))) as usize;
#[cfg(target_pointer_width = "64")]
pub const MAX_LENGTH_VALUE: usize = (std::u64::MAX >> (8 * (8 - BYTES_PER_LENGTH_OFFSET))) as usize;

/// The number of bytes used to indicate the variant of a union.
pub const BYTES_PER_UNION_SELECTOR: usize = 1;
/// The highest possible union selector value (higher values are reserved for backwards compatible
/// extensions).
pub const MAX_UNION_SELECTOR: u8 = 127;

/// Convenience function to SSZ encode an object supporting sszb::Encode.
///
/// Equivalent to `val.as_sszb_bytes()`.
pub fn sszb_encode<T>(val: &T) -> Vec<u8>
where
    T: Encode,
{
    val.as_sszb_bytes()
}
