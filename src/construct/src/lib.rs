// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

pub use construct_macros::Inline;
pub use proc_macro2::TokenStream;
pub use quote::quote;

pub trait Inline {
    fn inline(&self) -> TokenStream;
}

macro_rules! inline_primitive {
    ($x:ty) => {
        impl Inline for $x {
            fn inline(&self) -> TokenStream {
                quote! { #self }
            }
        }
    };
}

// Primitive implementations
// -----------------------------------------------------------------------------
impl<T: Inline, const N: usize> Inline for [T; N] {
    fn inline(&self) -> TokenStream {
        let values = self.iter().map(|x| x.inline());
        quote! {
            [ #(#values,)* ]
        }
    }
}
inline_primitive!(bool);
inline_primitive!(char);
inline_primitive!(f32);
inline_primitive!(f64);
inline_primitive!(i8);
inline_primitive!(i16);
inline_primitive!(i32);
inline_primitive!(i64);
inline_primitive!(i128);
inline_primitive!(isize);
inline_primitive!(str);
inline_primitive!(u8);
inline_primitive!(u16);
inline_primitive!(u32);
inline_primitive!(u64);
inline_primitive!(u128);
impl Inline for () {
    fn inline(&self) -> TokenStream {
        quote! {
            ()
        }
    }
}
inline_primitive!(usize);

// Collections implementations
// -----------------------------------------------------------------------------
impl<T: Inline> Inline for Vec<T> {
    fn inline(&self) -> TokenStream {
        let fields = self.iter().map(|x| x.inline());
        quote! {
            vec![#(#fields,)*]
        }
    }
}

// Misc implementations
// -----------------------------------------------------------------------------
impl<T> Inline for std::marker::PhantomData<T> {
    fn inline(&self) -> TokenStream {
        quote! {
            std::marker::PhantomData
        }
    }
}
impl Inline for String {
    fn inline(&self) -> TokenStream {
        quote! {
            String::from(#self)
        }
    }
}
impl<T: Inline> Inline for Option<T> {
    fn inline(&self) -> TokenStream {
        match self {
            None => quote! { None },
            Some(x) => {
                let a = x.inline();
                quote! { Some(#a) }
            }
        }
    }
}
impl<T: Inline, E: Inline> Inline for Result<T, E> {
    fn inline(&self) -> TokenStream {
        match self {
            Ok(ok) => {
                let a = ok.inline();
                quote! { Ok(#a) }
            }
            Err(err) => {
                let a = err.inline();
                quote! { Err(#a) }
            }
        }
    }
}

// We create implementations up to tuples of 128 elements.
construct_macros::derive_tuple!(128);

// Tests
// -----------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn primitive_test() {
        let a = 2u8;
        assert_eq!(a.inline().to_string(), quote! { 2u8 }.to_string())
    }
    #[test]
    fn vec_test() {
        let a: Vec<u8> = vec![1, 2, 3, 4, 5, 6, 7];
        assert_eq!(
            a.inline().to_string(),
            quote! { vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8,] }.to_string()
        )
    }
    #[test]
    fn str_test() {
        let a = "1 2 3 a b c 4 d";
        assert_eq!(format!("\"{}\"", a), a.inline().to_string());
    }
    #[test]
    fn string_test() {
        let a = String::from("1 2 3 a b c 4 d");
        assert_eq!(
            a.inline().to_string(),
            quote! { String::from("1 2 3 a b c 4 d") }.to_string()
        )
    }
}
