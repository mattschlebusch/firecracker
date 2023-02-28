// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};

#[cfg(cpuid)]
pub mod cpuid;

/// Module containing type implementations needed for aarch64 (ARM) CPU configuration
#[cfg(target_arch = "aarch64")]
pub mod aarch64;

/// Module containing type implementations needed for x86 CPU configuration
#[cfg(target_arch = "x86_64")]
pub mod x86;

/// Bit-mask based wrapper to apply
/// changes to a given register's value
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Modifier {
    /// Mask value is to be applied according
    /// to what is allowed through by the filter
    bit_mask_filter: u64,
    /// Mask value to be applied
    bit_mask_value: u64,
}
