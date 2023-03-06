// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::str::FromStr;

use serde::de::Error;
use serde::{Deserialize, Deserializer};

/// Types common for template definitions for both
/// Aarch64 and x86_64.

/// Bit-mask based wrapper to apply
/// changes to a given register's value
#[derive(Debug, Deserialize, Eq, PartialEq)]
pub struct RegisterModifier {
    /// Pointer of the location to be bit masked.
    #[serde(deserialize_with = "deserialize_u64_from_str")]
    addr: u64,
    /// Mask to be applied to register's value at the address
    /// provided.
    mask: BitMask,
}

/// Bit mask to adjust targeted bits to the value,
/// applied by the filter only.
#[derive(Debug, Deserialize, Eq, PartialEq)]
pub struct BitMask {
    /// Mask value is to be applied according
    /// to what is allowed through by the filter.
    #[serde(deserialize_with = "deserialize_u64_from_str")]
    filter: u64,
    /// Mask value to be applied.
    #[serde(deserialize_with = "deserialize_u64_from_str")]
    value: u64,
}

/// Generic struct for addressing registers
/// that are non-CPUID based.
#[derive(Debug, Deserialize, Eq, PartialEq)]
pub struct RegisterId {
    #[serde(deserialize_with = "deserialize_u64_from_str")]
    value: u64,
}

/// Guest config sub-module specifically useful for
/// config templates.
#[cfg(target_arch = "x86_64")]
pub mod x86_64 {
    use serde::Deserialize;

    use crate::guest_config::templates::RegisterModifier;

    /// CPUID register enumeration
    #[allow(unused)]
    #[allow(missing_docs)]
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub enum CpuidRegister {
        Eax,
        Ebx,
        Ecx,
        Edx,
    }

    /// Composite type that holistically provides
    /// the location of a specific register being used
    /// in the context of a CPUID tree.
    #[allow(unused)]
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct CpuidRegisterId {
        leaf: u32,
        subleaf: u32,
        flags: crate::guest_config::cpuid::cpuid_ffi::KvmCpuidFlags,
        pointer: CpuidRegister,
    }

    /// Wrapper type to containing x86_64 CPU config modifiers.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct X86_64CpuTemplate {
        /// Modifiers for CPUID configuration.
        // pub cpuid_modifiers: Vec<RegisterBitMask>,
        /// Modifiers for model specific registers.
        pub msr_modifiers: Vec<RegisterModifier>,
    }
}

/// Guest config sub-module specifically for
/// config templates.
#[cfg(target_arch = "aarch64")]
pub mod aarch64 {
    use serde::Deserialize;

    use crate::guest_config::templates::RegisterModifier;

    /// Wrapper type to containing aarch64 CPU config modifiers.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct Aarch64CpuTemplate {
        /// Modifiers for registers on Aarch64 CPUs.
        pub reg_modifiers: Vec<RegisterModifier>,
    }
}

fn deserialize_u64_from_str<'de, D>(deserializer: D) -> Result<u64, D::Error>
where
    D: Deserializer<'de>,
{
    let number_str = String::deserialize(deserializer)?;
    let deserialized_number: u64 = if number_str.len() > 2 {
        match &number_str[0..2] {
            "0b" => u64::from_str_radix(&number_str[2..], 2),
            "0x" => u64::from_str_radix(&number_str[2..], 16),
            _ => u64::from_str(&number_str),
        }
        .map_err(|err| {
            Error::custom(format!(
                "Failed to parse string [{}] as a number for CPU template - {:?}",
                number_str, err
            ))
        })?
    } else {
        u64::from_str(&number_str).map_err(|err| {
            Error::custom(format!(
                "Failed to parse string [{}] as a decimal number for CPU template - {:?}",
                number_str, err
            ))
        })?
    };

    Ok(deserialized_number)
}

fn deserialize_u32_from_str<'de, D>(deserializer: D) -> Result<u32, D::Error>
where
    D: Deserializer<'de>,
{
    let number_str = String::deserialize(deserializer)?;
    let deserialized_number: u32 = if number_str.len() > 2 {
        match &number_str[0..2] {
            "0b" => u32::from_str_radix(&number_str[2..], 2),
            "0x" => u32::from_str_radix(&number_str[2..], 16),
            _ => u32::from_str(&number_str),
        }
        .map_err(|err| {
            Error::custom(format!(
                "Failed to parse string [{}] as a number for CPU template - {:?}",
                number_str, err
            ))
        })?
    } else {
        u32::from_str(&number_str).map_err(|err| {
            Error::custom(format!(
                "Failed to parse string [{}] as a decimal number for CPU template - {:?}",
                number_str, err
            ))
        })?
    };

    Ok(deserialized_number)
}

#[cfg(test)]
mod tests {
    #[cfg(target_arch = "x86_64")]
    use crate::guest_config::templates::x86_64::X86_64CpuTemplate;

    #[cfg(target_arch = "x86_64")]
    const X86_64_TEMPLATE_JSON: &str = r#"{
        "msr_modifiers":  [
            {
                "addr": "0x0",
                "mask": {
                    "value": "0b0101",
                    "filter": "0b0111"
                }
            },
            {
                "addr": "0x1",
                "mask": {
                    "value": "0b0100",
                    "filter": "0b1111"
                }
            },
            {
                "addr": "2",
                "mask": {
                    "value": "0b0100",
                    "filter": "0b1111"
                }
            },
            {
                "addr": "0xbbca",
                "mask": {
                    "value": "0b0100",
                    "filter": "0x1111"
                }
            }
        ]
    }"#;

    #[cfg(target_arch = "aarch64")]
    use crate::guest_config::templates::aarch64::Aarch64CpuTemplate;

    #[cfg(target_arch = "aarch64")]
    const AARCH64_TEMPLATE_JSON: &str = r#"{
        "reg_modifiers":  [
            {
                "addr": "0x0AAC",
                "mask": {
                    "value": "0b0101",
                    "filter": "0b1111"
                }
            },
            {
                "addr": "0x0AAB",
                "mask": {
                    "value": "0b0110",
                    "filter": "0b1111"
                }
            }
        ]
    }"#;

    #[test]
    fn test_serialization_lifecycle() {
        #[cfg(target_arch = "x86_64")]
        {
            let cpu_config: X86_64CpuTemplate = serde_json::from_str(X86_64_TEMPLATE_JSON)
                .expect("Failed to deserialize x86_64 CPU template.");
            assert_eq!(4, cpu_config.msr_modifiers.len());
        }

        #[cfg(target_arch = "aarch64")]
        {
            let cpu_config: Aarch64CpuTemplate = serde_json::from_str(AARCH64_TEMPLATE_JSON)
                .expect("Failed to deserialize aarch64 CPU template.");

            assert_eq!(2, cpu_config.reg_modifiers.len());
        }
    }
}
