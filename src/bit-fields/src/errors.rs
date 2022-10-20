// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

/// Error type for `impl<T:std::fmt::Display> std::convert::TryFrom<std::collections::HashSet<T>>
/// for YourBitField`.
#[cfg(feature = "flag_set")]
// There will only ever be 1 possible error as a result of `TryFrom<HashSet<..>>`, thus we will
// never alter the layout of this struct.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TryFromFlagSetError;
#[cfg(feature = "flag_set")]
impl std::error::Error for TryFromFlagSetError {}
#[cfg(feature = "flag_set")]
impl fmt::Display for TryFromFlagSetError {
    /// ```
    /// assert_eq!(
    ///     bit_fields::TryFromFlagSetError.to_string(),
    ///     "Feature flag given in set which is not defined in bit field"
    /// );
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Feature flag given in set which is not defined in bit field"
        )
    }
}
/// Error type for `impl<T:std::fmt::Display>
/// std::convert::TryFrom<std::collections::HashMap<T,YourBitField>> for YourBitField`.
#[cfg(feature = "field_map")]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TryFromFieldMapError {
    /// Field given in map which is not defined in bit field.
    #[error("Field given in map which is not defined in bit field.")]
    UnknownField,
    /// Failed to assign value from field map.
    #[error("Failed to assign value from field map: {0}")]
    CheckedAssign(#[from] CheckedAssignError),
}
/// Error type for `impl<T:std::fmt::Display>
/// std::convert::TryFrom<(std::collections::HashSet<T>,std::collections::HashMap<T,YourBitField>)>
/// for YourBitField`.
#[cfg(all(feature = "flag_set", feature = "field_map"))]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TryFromFlagSetAndFieldMapError {
    /// Failed to parse flag set.
    #[error("Failed to parse flag set: {0}")]
    FlagSet(#[from] TryFromFlagSetError),
    /// Failed to parse field map.
    #[error("Failed to parse field map: {0}")]
    FieldMap(#[from] TryFromFieldMapError),
}

#[cfg(all(feature = "flag_set", feature = "field_map"))]
impl From<CheckedAssignError> for TryFromFlagSetAndFieldMapError {
    #[inline]
    fn from(err: CheckedAssignError) -> Self {
        Self::FieldMap(TryFromFieldMapError::CheckedAssign(err))
    }
}

/// Error type for [`BitRange<u8, _, _>::checked_add_assign`], [`BitRange<u16, _,
/// _>::checked_add_assign`], etc.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CheckedAddAssignError {
    /// Operation would result in overflow of bit range.
    #[error("Operation would result in overflow of bit range.")]
    Overflow,
    /// Given value is more than maximum value storable in bit range.
    #[error("Given value is more than maximum value storable in bit range.")]
    OutOfRange,
}

/// Error type for [`BitRange<u8, _, _>::checked_sub_assign`], [`BitRange<u16, _,
/// _>::checked_sub_assign`], etc.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CheckedSubAssignError {
    /// Operation would result in underflow of bit range.
    #[error("Operation would result in underflow of bit range.")]
    Underflow,
    /// Given value is more than maximum value storable in bit range.
    #[error("Given value is more than maximum value storable in bit range.")]
    OutOfRange,
}

/// Error type for [`BitRange<u8, _, _>::checked_assign`], [`BitRange<u16, _, _>::checked_assign`],
/// etc.
// There will only ever be 1 possible error as a result of `CheckedAssign`, thus we will never alter
// the layout of this struct.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedAssignError;
impl std::error::Error for CheckedAssignError {}
impl fmt::Display for CheckedAssignError {
    /// ```
    /// assert_eq!(
    ///     bit_fields::CheckedAssignError.to_string(),
    ///     "Given value is greater than maximum storable value in bit range"
    /// );
    /// ```
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Given value is greater than maximum storable value in bit range"
        )
    }
}
