// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::convert::TryFrom;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, DeriveInput};

/// Formats a given number into an alphabetical string.
fn format_radix(mut x: u32) -> String {
    let mut result = vec![];

    loop {
        let m = x % 25;
        x /= 25;
        // will panic if you use a bad radix (< 2 or > 36).
        result.push((m as u8 + 97) as char);
        if x == 0 {
            break;
        }
    }
    result.into_iter().rev().collect()
}

/// Generates tuple implementations for large tuples.
#[proc_macro]
pub fn derive_tuple(stream: TokenStream) -> TokenStream {
    let item = stream.into_iter().next().unwrap();
    let num: usize = match item {
        proc_macro::TokenTree::Literal(lit) => lit.to_string().parse().unwrap(),
        _ => unreachable!(),
    };
    // eprintln!("num: {}",num);

    let collected = (1..num)
        .map(|i| {
            let (values, generics): (Vec<_>, Vec<_>) = (0..i)
                .map(|j| {
                    (
                        format_ident!("__{}", format_radix(j as u32)),
                        format_ident!("__{}", format_radix(j as u32).to_uppercase()),
                    )
                })
                .unzip();
            let index = (0..i).map(syn::Index::from);

            quote! {
                impl<#(#generics:Inline,)*> Inline for (#(#generics,)*) {
                    fn inline(&self) -> TokenStream {
                        let (#(#values,)*) = (#(self.#index.inline(),)*);
                        quote! {
                            (#(##values,)*)
                        }
                    }
                }
            }
        })
        .collect::<proc_macro2::TokenStream>();

    // eprintln!("collected:\n{}",collected);

    TokenStream::from(collected)
}

/// Derives the [`construct::Inline`] trait.
#[proc_macro_derive(Inline)]
pub fn derive_inline(input: TokenStream) -> TokenStream {
    // Parse the input tokens into a syntax tree
    let input = parse_macro_input!(input as DeriveInput);

    // eprintln!("input: {:#?}",input);

    let ident = input.ident;
    let generics = input.generics.params;
    let generic_idents = generics.iter().map(|g| match g {
        syn::GenericParam::Type(x) => x.ident.clone(),
        syn::GenericParam::Lifetime(x) => x.lifetime.ident.clone(),
        syn::GenericParam::Const(x) => x.ident.clone(),
    });
    let expanded = match input.data {
        syn::Data::Struct(syn_struct) => {
            let inner = match syn_struct.fields {
                syn::Fields::Named(fields) => {
                    let (names, fields_inlined): (Vec<_>, Vec<_>) = fields
                        .named
                        .iter()
                        .map(|f| {
                            let field_ident = f
                                .ident
                                .as_ref()
                                .expect("Named struct fields should have names");
                            (
                                field_ident.clone(),
                                format_ident!("{}_inlined", field_ident),
                            )
                        })
                        .unzip();
                    quote! {
                        let (#(#fields_inlined,)*) = (#(self.#names.inline(),)*);
                        construct::quote! {
                            #ident {
                                #(
                                    #names: ##fields_inlined,
                                )*
                            }
                        }
                    }
                }
                syn::Fields::Unnamed(fields) => {
                    let (i, values): (Vec<_>, Vec<_>) = fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(i, _)| {
                            (
                                syn::Index::from(i),
                                format_ident!("__{}", format_radix(i as u32)),
                            )
                        })
                        .unzip();
                    quote! {
                        let (#(#values,)*) = (#(self.#i.inline(),)*);
                        construct::quote! {
                            #ident (
                                #(##values,)*
                            )
                        }
                    }
                }
                syn::Fields::Unit => quote! { construct::quote! { #ident } },
            };
            quote! {
                impl<#generics> construct::Inline for #ident<#(#generic_idents,)*> {
                    fn inline(&self) -> construct::TokenStream {
                        #inner
                    }
                }
            }
        }
        syn::Data::Enum(x) => {
            // panic!("Only structs are currently supported.")
            let matching = x.variants.iter().map(|v| {
                let variant_ident = v.ident.clone();
                match &v.fields {
                    syn::Fields::Unnamed(unnamed_fields) => {
                        let fields = unnamed_fields
                            .unnamed
                            .iter()
                            .enumerate()
                            .map(|(i, _)| {
                                let x = u8::try_from(i).expect(
                                    "Only up to 25 fields in an enum variant are supported.",
                                );
                                assert!(
                                    x < 25,
                                    "Only up to 25 fields in an enum variant are supported."
                                );
                                format_ident!("{}", (x + 97) as char)
                            })
                            .collect::<Vec<_>>();
                        let fields_inlined = fields
                            .iter()
                            .map(|f| format_ident!("{}_inlined", f))
                            .collect::<Vec<_>>();
                        quote! {
                            #ident::#variant_ident(#(#fields,)*) => {
                                let (#(#fields_inlined,)*) = (#(#fields.inline(),)*);
                                construct::quote! { #ident::#variant_ident(#(##fields_inlined,)*) }
                            }
                        }
                    }
                    syn::Fields::Unit => quote! {
                            #ident::#variant_ident => construct::quote! { #ident::#variant_ident }
                    },
                    syn::Fields::Named(_) => {
                        panic!("Named fields on enum variants are not supported.")
                    }
                }
            });
            quote! {
                impl<#generics> construct::Inline for #ident<#(#generic_idents,)*> {
                    fn inline(&self) -> construct::TokenStream {
                        match self {
                            #(
                                #matching,
                            )*
                        }
                    }
                }
            }
        }
        _ => panic!("Only structs are currently supported."),
    };

    // eprintln!("expanded:\n{}",expanded);

    TokenStream::from(expanded)
}
