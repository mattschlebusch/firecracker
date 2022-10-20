// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

/// Type used to ensure safety by avoiding some arithmetic operations.
///
/// Without this type we would parse and store the size of the bit field as a `u8`. The following
/// operations would then use the generic `u8` implementations which the compiler cannot guarantee
/// are safe. By using this enum to restrict the type we can avoid these operations. This is a
/// small point, but helps a little.
#[derive(Debug, Clone, Copy)]
pub enum DataType {
    /// `u8`
    U8 = 8,
    /// `u16`
    U16 = 16,
    /// `u32`
    U32 = 32,
    /// `u64`
    U64 = 64,
    /// `u128`
    U128 = 128,
}

impl DataType {
    // When const trait implementations are stabilized this should be
    // `impl const From<DataType> for u8`.
    /// Returns the size in bits of the data type.
    #[allow(clippy::as_conversions)]
    pub const fn size(self) -> u8 {
        self as u8
    }
}

impl fmt::Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::U8 => write!(f, "u8"),
            Self::U16 => write!(f, "u16"),
            Self::U32 => write!(f, "u32"),
            Self::U64 => write!(f, "u64"),
            Self::U128 => write!(f, "u128"),
        }
    }
}

impl std::str::FromStr for DataType {
    type Err = DataTypeTryFromError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "u8" => Ok(Self::U8),
            "u16" => Ok(Self::U16),
            "u32" => Ok(Self::U32),
            "u64" => Ok(Self::U64),
            "u128" => Ok(Self::U128),
            _ => Err(DataTypeTryFromError),
        }
    }
}

/// Error type for `impl TryFrom<&str> for DataType`
#[derive(Debug, PartialEq, Eq)]
pub struct DataTypeTryFromError;

impl fmt::Display for DataTypeTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Bad backing data type given. Only accepted types are `u8`, `u16`, `u32`, `u64` and \
             `u128`."
        )
    }
}

impl std::error::Error for DataTypeTryFromError {}

/// Utility used to assembly the display string
#[derive(Debug, Default)]
pub struct MultiLineString(pub Vec<String>);

impl MultiLineString {
    /// Pushes `MultiLineString` on to `self`, if the given `other` is deeper than `self` it will
    /// expand down to accommodate.
    pub fn push(&mut self, other: &Self) {
        // Split `other` into slice to join to `self` and slice to extend `self`.
        let (join, extend) = other.0.split_at(self.0.len());

        // Lines where both `self` and `other` have strings, join them
        let joined = self.0.iter().zip(join).map(|(x, y)| format!("{x}{y}"));

        // Lines `other` extends below `self` add them
        let chained = joined.chain(extend.iter().cloned());

        // Collect into new string
        self.0 = chained.collect();
    }
    /// Pushes a `&str` onto `self`.
    pub fn push_str(&mut self, s: &str) {
        self.push(&MultiLineString::from(s));
    }
}

impl From<&str> for MultiLineString {
    fn from(s: &str) -> Self {
        Self(s.split('\n').map(String::from).collect())
    }
}

impl fmt::Display for MultiLineString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for line in &self.0 {
            writeln!(f, "{}", line)?;
        }
        Ok(())
    }
}

/// An iterator over sub-slices of a given slice e.g. `[0..]`, `[1..]`, .., `[slice.len()-1..]`.
///
/// The last slice will always contain 1 element.
#[derive(Debug, Clone, Copy)]
pub struct SliceIter<'a, T> {
    /// The slice to iterate over.
    slice: &'a [T],
    /// The current index into the slice.
    position: usize,
}

// It would require violating borrowing rules for the arithmetic or slicing to fail.
//
// Someone would need to mutate a slice in a specific way while it is currently being
// iterated over to cause the arithmetic or slicing to fail.
#[allow(
    clippy::integer_arithmetic,
    clippy::arithmetic,
    clippy::indexing_slicing
)]
impl<'a, T> std::iter::Iterator for SliceIter<'a, T> {
    type Item = &'a [T];
    fn next(&mut self) -> Option<Self::Item> {
        if self.position == self.slice.len() {
            None
        } else {
            let s = &self.slice[self.position..];
            self.position += 1;
            Some(s)
        }
    }
}

impl<'a, T> From<&'a [T]> for SliceIter<'a, T> {
    fn from(slice: &'a [T]) -> Self {
        Self { slice, position: 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn slice_iter_empty() {
        let arr: Vec<u8> = vec![];
        let mut iter = SliceIter::from(arr.as_slice());
        assert_eq!(iter.next(), None);
    }
    #[test]
    fn slice_iter_single() {
        let arr: Vec<u8> = vec![1u8];
        let mut iter = SliceIter::from(arr.as_slice());
        assert_eq!(iter.next(), Some(vec![1u8].as_slice()));
    }
    #[test]
    fn slice_iter() {
        let arr = vec![1i32, 2i32, 3i32, 4i32, 5i32];
        let mut iter = SliceIter::from(arr.as_slice());
        assert_eq!(
            iter.next(),
            Some(vec![1i32, 2i32, 3i32, 4i32, 5i32].as_slice())
        );
        assert_eq!(iter.next(), Some(vec![2i32, 3i32, 4i32, 5i32].as_slice()));
        assert_eq!(iter.next(), Some(vec![3i32, 4i32, 5i32].as_slice()));
        assert_eq!(iter.next(), Some(vec![4i32, 5i32].as_slice()));
        assert_eq!(iter.next(), Some(vec![5i32].as_slice()));
        assert_eq!(iter.next(), None);
    }
    #[test]
    fn multi_line_string_match() {
        let mut mls = MultiLineString(Vec::new());
        mls.push_str("1 4\n2 5\n3 6");
        mls.push_str(" 7 10\n 8 11\n 9 12");
        assert_eq!(mls.to_string(), "1 4 7 10\n2 5 8 11\n3 6 9 12\n");
    }
    #[test]
    fn multi_line_string_mismatch() {
        let mut mls = MultiLineString(Vec::new());
        mls.push_str("1 2 3\n4 5 6");
        mls.push_str(" 7 10\n 8 11\n9 12");
        assert_eq!(mls.to_string(), "1 2 3 7 10\n4 5 6 8 11\n9 12\n");
    }
}
