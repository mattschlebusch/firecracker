// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::guest_config::Modifier;

/// Composite type that holistically provides
/// the location of a specific register being used
/// in the context of a CPUID tree
#[allow(unused)]
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct CpuidRegisterId {
    leaf: u32,
    subleaf: u32,
    pointer: CpuidRegister,
}

/// CPUID register enumeration
#[allow(unused)]
#[allow(missing_docs)]
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub enum CpuidRegister {
    Eax,
    Ebx,
    Ecx,
    Edx,
}

/// Template providing bitmask modifier info
/// for CPUID and MSRs.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct X86CpuTemplate {
    cpuid_modifiers: HashMap<CpuidRegisterId, Modifier>,
    /// Map of Modifiers for CPU configuration
    /// Key: Register pointer
    /// Value: Register's bitmask based modifier
    msr_modifiers: HashMap<u64, Modifier>,
}
