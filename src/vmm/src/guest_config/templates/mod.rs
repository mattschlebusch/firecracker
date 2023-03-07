// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::str::FromStr;

use serde::de::Error as SerdeError;
use serde::{Deserialize, Deserializer};

// TODO: Refactor code to merge deserialize_* functions for modules x86_64 and aarch64
/// Templates module to contain sub-modules for aarch64 and x86_64 templates

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
            SerdeError::custom(format!(
                "Failed to parse string [{}] as a number for CPU template - {:?}",
                number_str, err
            ))
        })?
    } else {
        u64::from_str(&number_str).map_err(|err| {
            SerdeError::custom(format!(
                "Failed to parse string [{}] as a decimal number for CPU template - {:?}",
                number_str, err
            ))
        })?
    };

    Ok(deserialized_number)
}

/// Errors thrown while configuring templates.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    /// Failure in processing the CPUID configuration.
    #[error("Error deserializing CPUID")]
    Cpuid,
    /// Unknown failure in processing the CPU template.
    #[error("Internal error processing CPU template")]
    Internal,
}

/// Guest config sub-module specifically useful for
/// config templates.
#[cfg(target_arch = "x86_64")]
pub mod x86_64 {
    use std::collections::{BTreeMap, HashMap};
    use std::str::FromStr;

    use serde::de::Error as SerdeError;
    use serde::{Deserialize, Deserializer};

    use crate::guest_config::cpuid::cpuid_ffi::KvmCpuidFlags;
    use crate::guest_config::cpuid::{
        AmdCpuid, Cpuid, CpuidEntry, CpuidKey, CpuidRegisters, IntelCpuid,
    };
    use crate::guest_config::templates::{deserialize_u64_from_str, Error};
    use crate::guest_config::x86_64::X86_64CpuConfiguration;

    /// CPUID register enumeration
    #[allow(missing_docs)]
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub enum CpuidRegister {
        Eax,
        Ebx,
        Ecx,
        Edx,
    }

    /// Target register to be modified by a mask.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct CpuidRegisterModifier {
        /// CPUID register to be modified by the bitmask.
        #[serde(deserialize_with = "deserialize_cpuid_register")]
        pub register: CpuidRegister,
        /// Mask to be applied to register's value at the address
        /// provided.
        pub mask: BitMask,
    }

    /// Composite type that holistically provides
    /// the location of a specific register being used
    /// in the context of a CPUID tree.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct CpuidLeafModifier {
        /// Leaf value.
        #[serde(deserialize_with = "deserialize_u32_from_str")]
        pub leaf: u32,
        /// Sub-Leaf value.
        #[serde(deserialize_with = "deserialize_u32_from_str")]
        pub subleaf: u32,
        /// KVM feature flags for this leaf-subleaf.
        #[serde(deserialize_with = "deserialize_kvm_cpuid_flags")]
        pub flags: crate::guest_config::cpuid::cpuid_ffi::KvmCpuidFlags,
        /// All registers to be modified under the sub-leaf.
        pub modifiers: Vec<CpuidRegisterModifier>,
    }

    /// Wrapper type to containing x86_64 CPU config modifiers.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct X86_64CpuTemplate {
        /// Modifiers for CPUID configuration.
        #[serde(default)]
        pub cpuid_modifiers: Vec<CpuidLeafModifier>,
        /// Modifiers for model specific registers.
        #[serde(default)]
        pub msr_modifiers: Vec<RegisterModifier>,
    }

    /// Bit mask to adjust targeted bits to the value,
    /// applied by the filter only.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct BitMask {
        /// Mask value is to be applied according
        /// to what is allowed through by the filter.
        #[serde(deserialize_with = "deserialize_u64_from_str")]
        pub filter: u64,
        /// Mask value to be applied.
        #[serde(deserialize_with = "deserialize_u64_from_str")]
        pub value: u64,
    }

    /// Bit-mask based wrapper to apply
    /// changes to a given register's value
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct RegisterModifier {
        /// Pointer of the location to be bit masked.
        #[serde(deserialize_with = "deserialize_u32_from_str")]
        pub addr: u32,
        /// Mask to be applied to register's value at the address
        /// provided.
        pub mask: BitMask,
    }

    /// CPU template with modifiers to be applied on
    /// top of an existing configuration to generate
    /// the guest configuration to be used.
    pub fn create_guest_cpu_config(
        template: &X86_64CpuTemplate,
        host_config: &X86_64CpuConfiguration,
    ) -> Result<X86_64CpuConfiguration, Error> {
        let mut guest_msrs_map: HashMap<u32, u64> = HashMap::new();
        let mut guest_cpuid_map: BTreeMap<CpuidKey, CpuidEntry>;

        // Get the hash map of CPUID data
        if host_config.cpuid.amd().is_some() {
            guest_cpuid_map = host_config.cpuid.amd().unwrap().0.clone();
        } else if host_config.cpuid.intel().is_some() {
            guest_cpuid_map = host_config.cpuid.intel().unwrap().0.clone();
        } else {
            return Err(Error::Cpuid);
        }

        // Apply CPUID modifiers
        for leaf_mod in &template.cpuid_modifiers {
            let cpuid_key = CpuidKey {
                leaf: leaf_mod.leaf,
                subleaf: leaf_mod.subleaf,
            };

            let cpuid_entry_option = guest_cpuid_map.get(&cpuid_key);
            let mut guest_cpuid_entry = if let Some(entry) = cpuid_entry_option {
                entry.clone()
            } else {
                CpuidEntry::default()
            };
            guest_cpuid_entry.flags = leaf_mod.flags;

            let (mut mod_eax, mut mod_ebx, mut mod_ecx, mut mod_edx) = (
                u64::from(guest_cpuid_entry.result.eax),
                u64::from(guest_cpuid_entry.result.ebx),
                u64::from(guest_cpuid_entry.result.ecx),
                u64::from(guest_cpuid_entry.result.edx),
            );

            for reg_mod in &leaf_mod.modifiers {
                match reg_mod.register {
                    CpuidRegister::Eax => mod_eax = apply_mask(Some(&mod_eax), &reg_mod.mask),
                    CpuidRegister::Ebx => mod_ebx = apply_mask(Some(&mod_ebx), &reg_mod.mask),
                    CpuidRegister::Ecx => mod_ecx = apply_mask(Some(&mod_ecx), &reg_mod.mask),
                    CpuidRegister::Edx => mod_edx = apply_mask(Some(&mod_edx), &reg_mod.mask),
                }
            }

            guest_cpuid_entry = CpuidEntry {
                flags: leaf_mod.flags,
                result: CpuidRegisters {
                    eax: mod_eax as u32,
                    ebx: mod_ebx as u32,
                    ecx: mod_ecx as u32,
                    edx: mod_edx as u32,
                },
            };

            guest_cpuid_map.insert(cpuid_key, guest_cpuid_entry);
        }

        // Apply MSR modifiers
        for modifier in &template.msr_modifiers {
            guest_msrs_map.insert(
                modifier.addr,
                apply_mask(host_config.msrs.get(&modifier.addr), &modifier.mask),
            );
        }

        if host_config.cpuid.amd().is_some() {
            Ok(X86_64CpuConfiguration {
                cpuid: Cpuid::Amd(AmdCpuid(guest_cpuid_map)),
                msrs: guest_msrs_map,
            })
        } else if host_config.cpuid.intel().is_some() {
            Ok(X86_64CpuConfiguration {
                cpuid: Cpuid::Intel(IntelCpuid(guest_cpuid_map)),
                msrs: guest_msrs_map,
            })
        } else {
            Err(Error::Internal)
        }
    }

    fn deserialize_kvm_cpuid_flags<'de, D>(deserializer: D) -> Result<KvmCpuidFlags, D::Error>
    where
        D: Deserializer<'de>,
    {
        let flag = u32::deserialize(deserializer)?;
        Ok(KvmCpuidFlags(flag))
    }

    fn deserialize_cpuid_register<'de, D>(deserializer: D) -> Result<CpuidRegister, D::Error>
    where
        D: Deserializer<'de>,
    {
        let cpuid_register_str = String::deserialize(deserializer)?;

        Ok(match cpuid_register_str.as_str() {
            "eax" => CpuidRegister::Eax,
            "ebx" => CpuidRegister::Ebx,
            "ecx" => CpuidRegister::Ecx,
            "edx" => CpuidRegister::Edx,
            _ => {
                return Err(D::Error::custom(
                    "Invalid CPUID register. Must be one of [eax, ebx, ecx, edx]",
                ))
            }
        })
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
                D::Error::custom(format!(
                    "Failed to parse string [{}] as a number for CPU template - {:?}",
                    number_str, err
                ))
            })?
        } else {
            u32::from_str(&number_str).map_err(|err| {
                D::Error::custom(format!(
                    "Failed to parse string [{}] as a decimal number for CPU template - {:?}",
                    number_str, err
                ))
            })?
        };

        Ok(deserialized_number)
    }

    fn apply_mask(source: Option<&u64>, mask: &BitMask) -> u64 {
        if let Some(value) = source {
            (value & !&mask.filter) | mask.value
        } else {
            mask.value
        }
    }
}

/// Guest config sub-module specifically for
/// config templates.
#[cfg(target_arch = "aarch64")]
pub mod aarch64 {
    use serde::Deserialize;

    /// Wrapper type to containing aarch64 CPU config modifiers.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct Aarch64CpuTemplate {
        /// Modifiers for registers on Aarch64 CPUs.
        pub reg_modifiers: Vec<RegisterModifier>,
    }

    /// Bit-mask based wrapper to apply
    /// changes to a given register's value
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct RegisterModifier {
        /// Pointer of the location to be bit masked.
        #[serde(deserialize_with = "deserialize_u64_from_str")]
        pub addr: u64,
        /// Mask to be applied to register's value at the address
        /// provided.
        pub mask: BitMask,
    }

    /// Bit mask to adjust targeted bits to the value,
    /// applied by the filter only.
    #[derive(Debug, Deserialize, Eq, PartialEq)]
    pub struct BitMask {
        /// Mask value is to be applied according
        /// to what is allowed through by the filter.
        #[serde(deserialize_with = "deserialize_u128_from_str")]
        pub filter: u128,
        /// Mask value to be applied.
        #[serde(deserialize_with = "deserialize_u128_from_str")]
        pub value: u128,
    }

    /// CPU template with modifiers to be applied on
    /// top of an existing configuration to generate
    /// the guest configuration to be used.
    pub fn create_guest_cpu_config(
        _template: &Aarch64CpuTemplate,
        _host_config: &Aarch64CpuConfiguration,
    ) -> Result<Aarch64CpuConfiguration, Error> {
        // TODO
        Ok(Aarch64CpuConfiguration::default())
    }

    fn deserialize_u128_from_str<'de, D>(deserializer: D) -> Result<u128, D::Error>
    where
        D: Deserializer<'de>,
    {
        let number_str = String::deserialize(deserializer)?;
        let deserialized_number: u128 = if number_str.len() > 2 {
            match &number_str[0..2] {
                "0b" => u128::from_str_radix(&number_str[2..], 2),
                "0x" => u128::from_str_radix(&number_str[2..], 16),
                _ => u128::from_str(&number_str),
            }
            .map_err(|err| {
                D::Error::custom(format!(
                    "Failed to parse string [{}] as a number for CPU template - {:?}",
                    number_str, err
                ))
            })?
        } else {
            u128::from_str(&number_str).map_err(|err| {
                D::Error::custom(format!(
                    "Failed to parse string [{}] as a decimal number for CPU template - {:?}",
                    number_str, err
                ))
            })?
        };

        Ok(deserialized_number)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(target_arch = "x86_64")]
    use kvm_bindings::KVM_CPUID_FLAG_STATEFUL_FUNC;
    #[cfg(target_arch = "x86_64")]
    use kvm_bindings::KVM_MAX_CPUID_ENTRIES;
    #[cfg(target_arch = "x86_64")]
    use kvm_ioctls::Kvm;

    #[cfg(target_arch = "x86_64")]
    use crate::guest_config::cpuid::KvmCpuidFlags;
    #[cfg(target_arch = "x86_64")]
    use crate::guest_config::cpuid::{Cpuid, RawCpuid};
    #[cfg(target_arch = "aarch64")]
    use crate::guest_config::templates::aarch64::{Aarch64CpuTemplate, BitMask, RegisterModifier};
    #[cfg(target_arch = "x86_64")]
    use crate::guest_config::templates::x86_64::{
        create_guest_cpu_config, BitMask, CpuidLeafModifier, CpuidRegister, CpuidRegisterModifier,
        RegisterModifier, X86_64CpuTemplate,
    };
    #[cfg(target_arch = "x86_64")]
    use crate::guest_config::x86_64::X86_64CpuConfiguration;

    #[cfg(target_arch = "x86_64")]
    const X86_64_TEMPLATE_JSON: &str = r#"{
        "cpuid_modifiers": [
            {
                "leaf": "0x80000001",
                "subleaf": "0x0007",
                "flags": 0,
                "modifiers": [
                    {
                        "register": "eax",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    }
                ]
            },
            {
                "leaf": "0x80000002",
                "subleaf": "0x0004",
                "flags": 0,
                "modifiers": [
                    {
                        "register": "ebx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    },
                    {
                        "register": "ecx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    }
                ]
            },
            {
                "leaf": "0x80000003",
                "subleaf": "0x0004",
                "flags": 0,
                "modifiers": [
                    {
                        "register": "edx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    }
                ]
            },
            {
                "leaf": "0x80000004",
                "subleaf": "0x0004",
                "flags": 0,
                "modifiers": [
                    {
                        "register": "edx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    },
                    {
                        "register": "ecx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    }
                ]
            },
            {
                "leaf": "0x80000005",
                "subleaf": "0x0004",
                "flags": 0,
                "modifiers": [
                    {
                        "register": "eax",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    },
                    {
                        "register": "edx",
                        "mask": {
                            "value": "0b0101",
                            "filter": "0b0111"
                        }
                    }
                ]
            }
        ],
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
            assert_eq!(5, cpu_config.cpuid_modifiers.len());
            assert_eq!(4, cpu_config.msr_modifiers.len());
        }

        #[cfg(target_arch = "aarch64")]
        {
            let cpu_config: Aarch64CpuTemplate = serde_json::from_str(AARCH64_TEMPLATE_JSON)
                .expect("Failed to deserialize aarch64 CPU template.");

            assert_eq!(2, cpu_config.reg_modifiers.len());
        }
    }

    #[test]
    fn test_empty_template() {
        #[cfg(target_arch = "x86_64")]
        {
            let host_configuration = supported_cpu_config();

            let template = X86_64CpuTemplate {
                cpuid_modifiers: vec![],
                msr_modifiers: vec![],
            };

            let guest_config_result = create_guest_cpu_config(&template, &host_configuration);
            assert!(
                guest_config_result.is_ok(),
                "{}",
                guest_config_result.unwrap_err()
            );
            assert_eq!(guest_config_result.unwrap(), host_configuration);
        }

        // TODO - Aarch64 test
        // #[cfg(target_arch = "aarch64")]
    }

    #[test]
    fn test_template() {
        #[cfg(target_arch = "x86_64")]
        {
            let host_configuration = supported_cpu_config();

            let template = X86_64CpuTemplate {
                cpuid_modifiers: Vec::from([CpuidLeafModifier {
                    leaf: 0x1,
                    subleaf: 0x1,
                    flags: KvmCpuidFlags(KVM_CPUID_FLAG_STATEFUL_FUNC),
                    modifiers: Vec::from([
                        CpuidRegisterModifier {
                            register: CpuidRegister::Eax,
                            mask: BitMask {
                                filter: 0,
                                value: 0,
                            },
                        },
                        CpuidRegisterModifier {
                            register: CpuidRegister::Eax,
                            mask: BitMask {
                                filter: 0,
                                value: 0,
                            },
                        },
                    ]),
                }]),
                msr_modifiers: Vec::from([RegisterModifier {
                    addr: 0x8000,
                    mask: BitMask {
                        filter: 0,
                        value: 0,
                    },
                }]),
            };

            let guest_config_result = create_guest_cpu_config(&template, &host_configuration);
            assert!(
                guest_config_result.is_ok(),
                "{}",
                guest_config_result.unwrap_err()
            );
            assert_ne!(guest_config_result.unwrap(), host_configuration);
        }

        // TODO - Aarch64 test
        // #[cfg(target_arch = "aarch64")]
    }

    #[cfg(target_arch = "x86_64")]
    fn supported_cpu_config() -> X86_64CpuConfiguration {
        let kvm_result = Kvm::new();
        assert!(kvm_result.is_ok(), "Unable to access KVM");

        // Create descriptor KVM resource's file descriptor
        let vm_fd_result = kvm_result.as_ref().unwrap().create_vm();
        assert!(vm_fd_result.is_ok(), "{}", vm_fd_result.unwrap_err());

        let kvm_cpuid_result = kvm_result
            .unwrap()
            .get_supported_cpuid(KVM_MAX_CPUID_ENTRIES);
        assert!(
            kvm_cpuid_result.is_ok(),
            "{}",
            kvm_cpuid_result.unwrap_err()
        );
        let kvm_cpuid = kvm_cpuid_result.unwrap();
        let raw_cpuid = RawCpuid::from(kvm_cpuid);
        let cpuid_result = Cpuid::try_from(raw_cpuid);
        assert!(cpuid_result.is_ok(), "{}", cpuid_result.unwrap_err());
        X86_64CpuConfiguration {
            cpuid: cpuid_result.unwrap(),
            msrs: Default::default(),
        }
    }
}
