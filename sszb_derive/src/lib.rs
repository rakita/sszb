#![recursion_limit = "256"]
//! Provides procedural derive macros for the `Encode` and `Decode` traits of the `eth2_sszb` crate.
//!
//! Supports field attributes, see each derive macro for more information.

use darling::{FromDeriveInput, FromMeta};
use proc_macro::TokenStream;
use quote::quote;
use std::convert::TryInto;
use syn::{parse_macro_input, DataEnum, DataStruct, DeriveInput, Ident};

/// The highest possible union selector value (higher values are reserved for backwards compatible
/// extensions).
const MAX_UNION_SELECTOR: u8 = 127;

#[derive(Debug, FromDeriveInput)]
#[darling(attributes(sszb))]
struct StructOpts {
    #[darling(default)]
    enum_behaviour: Option<String>,
}

/// Field-level configuration.
#[derive(Debug, Default, FromMeta)]
struct FieldOpts {
    #[darling(default)]
    with: Option<Ident>,
    #[darling(default)]
    skip_serializing: bool,
    #[darling(default)]
    skip_deserializing: bool,
}

const ENUM_TRANSPARENT: &str = "transparent";
const ENUM_UNION: &str = "union";
const ENUM_VARIANTS: &[&str] = &[ENUM_TRANSPARENT, ENUM_UNION];
const NO_ENUM_BEHAVIOUR_ERROR: &str = "enums require an \"enum_behaviour\" attribute, \
    e.g., #[sszb(enum_behaviour = \"transparent\")]";

enum EnumBehaviour {
    Transparent,
    Union,
}

impl EnumBehaviour {
    pub fn new(s: Option<String>) -> Option<Self> {
        s.map(|s| match s.as_ref() {
            ENUM_TRANSPARENT => EnumBehaviour::Transparent,
            ENUM_UNION => EnumBehaviour::Union,
            other => panic!(
                "{} is an invalid enum_behaviour, use either {:?}",
                other, ENUM_VARIANTS
            ),
        })
    }
}

fn parse_sszb_fields(struct_data: &syn::DataStruct) -> Vec<(&syn::Type, &syn::Ident, FieldOpts)> {
    struct_data
        .fields
        .iter()
        .map(|field| {
            let ty = &field.ty;
            let ident = match &field.ident {
                Some(ref ident) => ident,
                _ => panic!("sszb_derive only supports named struct fields."),
            };

            let field_opts_candidates = field
                .attrs
                .iter()
                .filter(|attr| {
                    attr.path
                        .get_ident()
                        .map_or(false, |ident| *ident == "sszb")
                })
                .collect::<Vec<_>>();

            if field_opts_candidates.len() > 1 {
                panic!("more than one field-level \"sszb\" attribute provided")
            }

            let field_opts = field_opts_candidates
                .first()
                .map(|attr| {
                    let meta = attr.parse_meta().unwrap();
                    FieldOpts::from_meta(&meta).unwrap()
                })
                .unwrap_or_default();

            (ty, ident, field_opts)
        })
        .collect()
}

/// Implements `sszb::Encode` for some `struct` or `enum`.
#[proc_macro_derive(Encode, attributes(sszb))]
pub fn sszb_encode_derive(input: TokenStream) -> TokenStream {
    let item = parse_macro_input!(input as DeriveInput);
    let opts = StructOpts::from_derive_input(&item).unwrap();
    let enum_opt = EnumBehaviour::new(opts.enum_behaviour);

    match &item.data {
        syn::Data::Struct(s) => {
            if enum_opt.is_some() {
                panic!("enum_behaviour is invalid for structs");
            }
            sszb_encode_derive_struct(&item, s)
        }
        syn::Data::Enum(s) => match enum_opt.expect(NO_ENUM_BEHAVIOUR_ERROR) {
            EnumBehaviour::Transparent => sszb_encode_derive_enum_transparent(&item, s),
            EnumBehaviour::Union => sszb_encode_derive_enum_union(&item, s),
        },
        _ => panic!("sszb_derive only supports structs and enums"),
    }
}

/// Derive `sszb::Encode` for a struct.
///
/// Fields are encoded in the order they are defined.
///
/// ## Field attributes
///
/// - `#[sszb(skip_serializing)]`: the field will not be serialized.
fn sszb_encode_derive_struct(derive_input: &DeriveInput, struct_data: &DataStruct) -> TokenStream {
    let name = &derive_input.ident;
    let (impl_generics, ty_generics, where_clause) = &derive_input.generics.split_for_impl();

    let field_is_sszb_fixed_len = &mut vec![];
    let field_fixed_len = &mut vec![];
    let field_sszb_bytes_len = &mut vec![];
    let field_encoder_append = &mut vec![];

    for (ty, ident, field_opts) in parse_sszb_fields(struct_data) {
        if field_opts.skip_serializing {
            continue;
        }

        if let Some(module) = field_opts.with {
            let module = quote! { #module::encode };
            field_is_sszb_fixed_len.push(quote! { #module::is_sszb_fixed_len() });
            field_fixed_len.push(quote! { #module::sszb_fixed_len() });
            field_sszb_bytes_len.push(quote! { #module::sszb_bytes_len(&self.#ident) });
            field_encoder_append.push(quote! {
                encoder.append_parameterized(
                    #module::is_sszb_fixed_len(),
                    |buf| #module::sszb_append(&self.#ident, buf)
                )
            });
        } else {
            field_is_sszb_fixed_len.push(quote! { <#ty as sszb::Encode>::is_sszb_fixed_len() });
            field_fixed_len.push(quote! { <#ty as sszb::Encode>::sszb_fixed_len() });
            field_sszb_bytes_len.push(quote! { self.#ident.sszb_bytes_len() });
            field_encoder_append.push(quote! { encoder.append(&self.#ident) });
        }
    }

    let output = quote! {
        impl #impl_generics sszb::Encode for #name #ty_generics #where_clause {
            fn is_sszb_fixed_len() -> bool {
                #(
                    #field_is_sszb_fixed_len &&
                )*
                    true
            }

            fn sszb_fixed_len() -> usize {
                if <Self as sszb::Encode>::is_sszb_fixed_len() {
                    let mut len: usize = 0;
                    #(
                        len = len
                            .checked_add(#field_fixed_len)
                            .expect("encode sszb_fixed_len length overflow");
                    )*
                    len
                } else {
                    sszb::BYTES_PER_LENGTH_OFFSET
                }
            }

            fn sszb_bytes_len(&self) -> usize {
                if <Self as sszb::Encode>::is_sszb_fixed_len() {
                    <Self as sszb::Encode>::sszb_fixed_len()
                } else {
                    let mut len: usize = 0;
                    #(
                        if #field_is_sszb_fixed_len {
                            len = len
                                .checked_add(#field_fixed_len)
                                .expect("encode sszb_bytes_len length overflow");
                        } else {
                            len = len
                                .checked_add(sszb::BYTES_PER_LENGTH_OFFSET)
                                .expect("encode sszb_bytes_len length overflow for offset");
                            len = len
                                .checked_add(#field_sszb_bytes_len)
                                .expect("encode sszb_bytes_len length overflow for bytes");
                        }
                    )*

                    len
                }
            }

            fn sszb_append(&self, buf: &mut Vec<u8>) {
                let mut offset: usize = 0;
                #(
                    offset = offset
                        .checked_add(#field_fixed_len)
                        .expect("encode sszb_append offset overflow");
                )*
                let mut encoder = sszb::SszEncoder::container(buf, offset);

                #(
                    #field_encoder_append;
                )*

                encoder.finalize();
            }
        }
    };
    output.into()
}

/// Derive `sszb::Encode` for an enum in the "transparent" method.
///
/// The "transparent" method is distinct from the "union" method specified in the SSZB specification.
/// When using "transparent", the enum will be ignored and the contained field will be serialized as
/// if the enum does not exist. Since an union variant "selector" is not serialized, it is not
/// possible to reliably decode an enum that is serialized transparently.
///
/// ## Limitations
///
/// Only supports:
/// - Enums with a single field per variant, where
///     - All fields are variably sized from an SSZB-perspective (not fixed size).
///
/// ## Panics
///
/// Will panic at compile-time if the single field requirement isn't met, but will panic *at run
/// time* if the variable-size requirement isn't met.
fn sszb_encode_derive_enum_transparent(
    derive_input: &DeriveInput,
    enum_data: &DataEnum,
) -> TokenStream {
    let name = &derive_input.ident;
    let (impl_generics, ty_generics, where_clause) = &derive_input.generics.split_for_impl();

    let (patterns, assert_exprs): (Vec<_>, Vec<_>) = enum_data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;

            if variant.fields.len() != 1 {
                panic!("sszb::Encode can only be derived for enums with 1 field per variant");
            }

            let pattern = quote! {
                #name::#variant_name(ref inner)
            };

            let ty = &(&variant.fields).into_iter().next().unwrap().ty;
            let type_assert = quote! {
                !<#ty as sszb::Encode>::is_sszb_fixed_len()
            };
            (pattern, type_assert)
        })
        .unzip();

    let output = quote! {
        impl #impl_generics sszb::Encode for #name #ty_generics #where_clause {
            fn is_sszb_fixed_len() -> bool {
                assert!(
                    #(
                        #assert_exprs &&
                    )* true,
                    "not all enum variants are variably-sized"
                );
                false
            }

            fn sszb_bytes_len(&self) -> usize {
                match self {
                    #(
                        #patterns => inner.sszb_bytes_len(),
                    )*
                }
            }

            fn sszb_append(&self, buf: &mut Vec<u8>) {
                match self {
                    #(
                        #patterns => inner.sszb_append(buf),
                    )*
                }
            }
        }
    };
    output.into()
}

/// Derive `sszb::Encode` for an `enum` following the "union" SSZB spec.
///
/// The union selector will be determined based upon the order in which the enum variants are
/// defined. E.g., the top-most variant in the enum will have a selector of `0`, the variant
/// beneath it will have a selector of `1` and so on.
///
/// # Limitations
///
/// Only supports enums where each variant has a single field.
fn sszb_encode_derive_enum_union(derive_input: &DeriveInput, enum_data: &DataEnum) -> TokenStream {
    let name = &derive_input.ident;
    let (impl_generics, ty_generics, where_clause) = &derive_input.generics.split_for_impl();

    let patterns: Vec<_> = enum_data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;

            if variant.fields.len() != 1 {
                panic!("sszb::Encode can only be derived for enums with 1 field per variant");
            }

            let pattern = quote! {
                #name::#variant_name(ref inner)
            };
            pattern
        })
        .collect();

    let union_selectors = compute_union_selectors(patterns.len());

    let output = quote! {
        impl #impl_generics sszb::Encode for #name #ty_generics #where_clause {
            fn is_sszb_fixed_len() -> bool {
                false
            }

            fn sszb_bytes_len(&self) -> usize {
                match self {
                    #(
                        #patterns => inner
                            .sszb_bytes_len()
                            .checked_add(1)
                            .expect("encoded length must be less than usize::max_value"),
                    )*
                }
            }

            fn sszb_append(&self, buf: &mut Vec<u8>) {
                match self {
                    #(
                        #patterns => {
                            let union_selector: u8 = #union_selectors;
                            debug_assert!(union_selector <= sszb::MAX_UNION_SELECTOR);
                            buf.push(union_selector);
                            inner.sszb_append(buf)
                        },
                    )*
                }
            }
        }
    };
    output.into()
}

/// Derive `sszb::Decode` for a struct or enum.
#[proc_macro_derive(Decode, attributes(sszb))]
pub fn sszb_decode_derive(input: TokenStream) -> TokenStream {
    let item = parse_macro_input!(input as DeriveInput);
    let opts = StructOpts::from_derive_input(&item).unwrap();
    let enum_opt = EnumBehaviour::new(opts.enum_behaviour);

    match &item.data {
        syn::Data::Struct(s) => {
            if enum_opt.is_some() {
                panic!("enum_behaviour is invalid for structs");
            }
            sszb_decode_derive_struct(&item, s)
        }
        syn::Data::Enum(s) => match enum_opt.expect(NO_ENUM_BEHAVIOUR_ERROR) {
            EnumBehaviour::Transparent => panic!(
                "Decode cannot be derived for enum_behaviour \"{}\", only \"{}\" is valid.",
                ENUM_TRANSPARENT, ENUM_UNION
            ),
            EnumBehaviour::Union => sszb_decode_derive_enum_union(&item, s),
        },
        _ => panic!("sszb_derive only supports structs and enums"),
    }
}

/// Implements `sszb::Decode` for some `struct`.
///
/// Fields are decoded in the order they are defined.
///
/// ## Field attributes
///
/// - `#[sszb(skip_deserializing)]`: during de-serialization the field will be instantiated from a
/// `Default` implementation. The decoder will assume that the field was not serialized at all
/// (e.g., if it has been serialized, an error will be raised instead of `Default` overriding it).
fn sszb_decode_derive_struct(item: &DeriveInput, struct_data: &DataStruct) -> TokenStream {
    let name = &item.ident;
    let (impl_generics, ty_generics, where_clause) = &item.generics.split_for_impl();

    let mut register_types = vec![];
    let mut field_names = vec![];
    let mut fixed_decodes = vec![];
    let mut decodes = vec![];
    let mut is_fixed_lens = vec![];
    let mut fixed_lens = vec![];

    for (ty, ident, field_opts) in parse_sszb_fields(struct_data) {
        field_names.push(quote! {
            #ident
        });

        // Field should not be deserialized; use a `Default` impl to instantiate.
        if field_opts.skip_deserializing {
            decodes.push(quote! {
                let #ident = <_>::default();
            });

            fixed_decodes.push(quote! {
                let #ident = <_>::default();
            });

            continue;
        }

        let is_sszb_fixed_len;
        let sszb_fixed_len;
        let from_sszb_bytes;
        if let Some(module) = field_opts.with {
            let module = quote! { #module::decode };

            is_sszb_fixed_len = quote! { #module::is_sszb_fixed_len() };
            sszb_fixed_len = quote! { #module::sszb_fixed_len() };
            from_sszb_bytes = quote! { #module::from_sszb_bytes(slice) };

            register_types.push(quote! {
                builder.register_type_parameterized(#is_sszb_fixed_len, #sszb_fixed_len)?;
            });
            decodes.push(quote! {
                let #ident = decoder.decode_next_with(|slice| #module::from_sszb_bytes(slice))?;
            });
        } else {
            is_sszb_fixed_len = quote! { <#ty as sszb::Decode>::is_sszb_fixed_len() };
            sszb_fixed_len = quote! { <#ty as sszb::Decode>::sszb_fixed_len() };
            from_sszb_bytes = quote! { <#ty as sszb::Decode>::from_sszb_bytes(slice) };

            register_types.push(quote! {
                builder.register_type::<#ty>()?;
            });
            decodes.push(quote! {
                let #ident = decoder.decode_next()?;
            });
        }

        fixed_decodes.push(quote! {
            let #ident = {
                start = end;
                end = end
                    .checked_add(#sszb_fixed_len)
                    .ok_or_else(|| sszb::DecodeError::OutOfBoundsByte {
                        i: usize::max_value()
                    })?;
                let slice = bytes.get(start..end)
                    .ok_or_else(|| sszb::DecodeError::InvalidByteLength {
                        len: bytes.len(),
                        expected: end
                    })?;
                #from_sszb_bytes?
            };
        });
        is_fixed_lens.push(is_sszb_fixed_len);
        fixed_lens.push(sszb_fixed_len);
    }

    let output = quote! {
        impl #impl_generics sszb::Decode for #name #ty_generics #where_clause {
            fn is_sszb_fixed_len() -> bool {
                #(
                    #is_fixed_lens &&
                )*
                    true
            }

            fn sszb_fixed_len() -> usize {
                if <Self as sszb::Decode>::is_sszb_fixed_len() {
                    let mut len: usize = 0;
                    #(
                        len = len
                            .checked_add(#fixed_lens)
                            .expect("decode sszb_fixed_len overflow");
                    )*
                    len
                } else {
                    sszb::BYTES_PER_LENGTH_OFFSET
                }
            }

            fn from_sszb_bytes(bytes: &[u8]) -> std::result::Result<Self, sszb::DecodeError> {
                if <Self as sszb::Decode>::is_sszb_fixed_len() {
                    if bytes.len() != <Self as sszb::Decode>::sszb_fixed_len() {
                        return Err(sszb::DecodeError::InvalidByteLength {
                            len: bytes.len(),
                            expected: <Self as sszb::Decode>::sszb_fixed_len(),
                        });
                    }

                    let mut start: usize = 0;
                    let mut end = start;

                    #(
                        #fixed_decodes
                    )*

                    Ok(Self {
                        #(
                            #field_names,
                        )*
                    })
                } else {
                    let mut builder = sszb::SszDecoderBuilder::new(bytes);

                    #(
                        #register_types
                    )*

                    let mut decoder = builder.build()?;

                    #(
                        #decodes
                    )*


                    Ok(Self {
                        #(
                            #field_names,
                        )*
                    })
                }
            }
        }
    };
    output.into()
}

/// Derive `sszb::Decode` for an `enum` following the "union" SSZB spec.
fn sszb_decode_derive_enum_union(derive_input: &DeriveInput, enum_data: &DataEnum) -> TokenStream {
    let name = &derive_input.ident;
    let (impl_generics, ty_generics, where_clause) = &derive_input.generics.split_for_impl();

    let (constructors, var_types): (Vec<_>, Vec<_>) = enum_data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;

            if variant.fields.len() != 1 {
                panic!("sszb::Encode can only be derived for enums with 1 field per variant");
            }

            let constructor = quote! {
                #name::#variant_name
            };

            let ty = &(&variant.fields).into_iter().next().unwrap().ty;
            (constructor, ty)
        })
        .unzip();

    let union_selectors = compute_union_selectors(constructors.len());

    let output = quote! {
        impl #impl_generics sszb::Decode for #name #ty_generics #where_clause {
            fn is_sszb_fixed_len() -> bool {
                false
            }

            fn from_sszb_bytes(bytes: &[u8]) -> Result<Self, sszb::DecodeError> {
                // Sanity check to ensure the definition here does not drift from the one defined in
                // `sszb`.
                debug_assert_eq!(#MAX_UNION_SELECTOR, sszb::MAX_UNION_SELECTOR);

                let (selector, body) = sszb::split_union_bytes(bytes)?;

                match selector.into() {
                    #(
                        #union_selectors => {
                            <#var_types as sszb::Decode>::from_sszb_bytes(body).map(#constructors)
                        },
                    )*
                    other => Err(sszb::DecodeError::UnionSelectorInvalid(other))
                }
            }
        }
    };
    output.into()
}

fn compute_union_selectors(num_variants: usize) -> Vec<u8> {
    let union_selectors = (0..num_variants)
        .map(|i| {
            i.try_into()
                .expect("union selector exceeds u8::max_value, union has too many variants")
        })
        .collect::<Vec<u8>>();

    let highest_selector = union_selectors
        .last()
        .copied()
        .expect("0-variant union is not permitted");

    assert!(
        highest_selector <= MAX_UNION_SELECTOR,
        "union selector {} exceeds limit of {}, enum has too many variants",
        highest_selector,
        MAX_UNION_SELECTOR
    );

    union_selectors
}
