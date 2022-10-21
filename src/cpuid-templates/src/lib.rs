// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use cpuid::{intel::*, Cpuid, FixedString};
lazy_static::lazy_static! { pub static ref T2 : Cpuid = include ! ("t2.in") ; pub static ref C3 : Cpuid = include ! ("c3.in") ; pub static ref T2S : Cpuid = include ! ("t2s.in") ; }
#[cfg(test)]
mod tests {
    use super::*;
    use cpuid::Cpuid;
    #[test]
    fn t2_test() {
        let string = std::fs::read_to_string("./templates/t2.json").unwrap();
        let now = std::time::Instant::now();
        serde_json::from_str::<Cpuid>(&string).unwrap();
        let deserialize_elapsed = now.elapsed();
        dbg!(&deserialize_elapsed);
        let now = std::time::Instant::now();
        lazy_static::initialize(&T2);
        let allocate_elapsed = now.elapsed();
        dbg!(&allocate_elapsed);
        assert!(allocate_elapsed < deserialize_elapsed.mul_f32(0.05f32));
    }
    #[test]
    fn c3_test() {
        let string = std::fs::read_to_string("./templates/c3.json").unwrap();
        let now = std::time::Instant::now();
        serde_json::from_str::<Cpuid>(&string).unwrap();
        let deserialize_elapsed = now.elapsed();
        dbg!(&deserialize_elapsed);
        let now = std::time::Instant::now();
        lazy_static::initialize(&C3);
        let allocate_elapsed = now.elapsed();
        dbg!(&allocate_elapsed);
        assert!(allocate_elapsed < deserialize_elapsed.mul_f32(0.05f32));
    }
    #[test]
    fn t2s_test() {
        let string = std::fs::read_to_string("./templates/t2s.json").unwrap();
        let now = std::time::Instant::now();
        serde_json::from_str::<Cpuid>(&string).unwrap();
        let deserialize_elapsed = now.elapsed();
        dbg!(&deserialize_elapsed);
        let now = std::time::Instant::now();
        lazy_static::initialize(&T2S);
        let allocate_elapsed = now.elapsed();
        dbg!(&allocate_elapsed);
        assert!(allocate_elapsed < deserialize_elapsed.mul_f32(0.05f32));
    }
}
