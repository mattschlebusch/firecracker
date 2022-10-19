// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io::Write;

use construct::Inline;
use proc_macro2::TokenStream;
use quote::quote;

/// In tests we assert that the time it took to instantiate the lazy static with inline code is less
/// than `DELTA*x` where `x` is the time it took to deserialize the template from json.
const DELTA: f32 = 0.05f32;

/// License to write into auto-generated `lib.rs`.
const LICENSE: &str = "// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.\n// SPDX-License-Identifier: Apache-2.0\n\n";

fn main() {
    let template_dir = std::fs::read_dir("./templates").unwrap();

    let (statics, tests): (TokenStream, TokenStream) = template_dir
        .map(|template_entry| {
            let template_path = template_entry.unwrap().path();
            // Re-build if this template file changed.
            println!("cargo:rerun-if-changed={}", template_path.display());
            // Get file contents as string.
            let string = std::fs::read_to_string(&template_path).unwrap();
            // Deserialize json string to cpuid structure.
            let cpuid = serde_json::from_str::<cpuid::Cpuid>(&string).unwrap();
            // Get rust code that allocate this specific cpuid structure.
            let inline = cpuid.inline();

            // Get identifier
            let identifier = template_path
                .as_path()
                .file_stem()
                .unwrap()
                .to_str()
                .unwrap();
            // Get identifier in uppercase
            let uppercase_identifier = identifier.to_uppercase();

            // Create construction code file
            {
                // Create `<template>.in` file under `src/`
                let mut template_file = std::fs::OpenOptions::new()
                    .write(true)
                    .truncate(true)
                    .create(true)
                    .open(format!("./src/{}.in", identifier))
                    .unwrap();
                // Write to template file
                template_file
                    .write_all(inline.to_string().as_bytes())
                    .unwrap();
            }

            // Append static
            let statics = {
                let ident = quote::format_ident!("{}", uppercase_identifier);
                let file = format!("{}.in", identifier);
                quote! {
                    pub static ref #ident: Cpuid = include!(#file);
                }
            };

            // Create initialization speed test
            let tests = {
                let test_fn = quote::format_ident!("{}_test", identifier);
                let path = format!("./templates/{identifier}.json");
                let uppercase_ident = quote::format_ident!("{}", uppercase_identifier);
                quote! {
                    #[test]
                    fn #test_fn() {
                        let string = std::fs::read_to_string(#path).unwrap();
                        let now = std::time::Instant::now();
                        serde_json::from_str::<Cpuid>(&string).unwrap();
                        let deserialize_elapsed = now.elapsed();
                        dbg!(&deserialize_elapsed);

                        let now = std::time::Instant::now();
                        lazy_static::initialize(&#uppercase_ident);
                        let allocate_elapsed = now.elapsed();
                        dbg!(&allocate_elapsed);

                        assert!(allocate_elapsed < deserialize_elapsed.mul_f32(#DELTA));
                    }
                }
            };

            (statics, tests)
        })
        .unzip();

    let lib = quote! {
        use cpuid::{intel::*, FixedString, Cpuid};

        lazy_static::lazy_static! {
            #statics
        }

        #[cfg(test)]
        mod tests {
            use super::*;
            use cpuid::Cpuid;
            #tests
        }
    };

    // Make lib.rs
    let mut lib_file = std::fs::OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open("./src/lib.rs")
        .unwrap();
    lib_file.write_all(LICENSE.as_bytes()).unwrap();
    lib_file.write_all(lib.to_string().as_bytes()).unwrap();

    // Format lib.rs
    std::process::Command::new("cargo")
        .arg("fmt")
        .output()
        .unwrap();
}
