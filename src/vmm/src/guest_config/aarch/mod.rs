// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::guest_config::Modifier;

/// Template providing bitmask modifier info
/// for CPU register configuration.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ArmCpuTemplate {
    /// Map of Modifiers for CPU configuration
    /// Key: Register pointer
    /// Value: Register's bitmask based modifier
    pub modifiers: HashMap<u64, Modifier>,
}
