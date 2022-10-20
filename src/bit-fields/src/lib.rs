// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A macro to generate structures which support bit flags and sub-bytes ranges.
//!
//! A [bitflags](https://crates.io/crates/bitflags) like library which also supports value ranges.
//!
//! Originally designed to support efficiently interacting with [CPUID](https://en.wikipedia.org/wiki/CPUID).
//!
//! See [`ExampleBitField`] for an example.
//!
//! ## Features
//! - `set_theory`: Set theory functions, these are `superset`, `subset`, `disjoint`, `intersection`
//!   and `union`.
//! - `bit_index`: Bit indexing, allowing constant indexing like `.bit::<3>()` and
//!   `.bit_mut::<3>()`.
//! - `flag_set`: Flag set interoperability, allowing converting to and form a hashset of strings
//!   referring to bit flags.
//! - `field_map`: Field map interoperability, allowing converting to and from a hashmap of string
//!   field names and data type field values.
//! - `display`: `std::fmt::Display` implementation.
//! - `cmp_flags`: The `cmp_flags` function which can be used to compare bit flags of 2 bit field
//!   structures.
//! - `serde`: Serde serialize and deserialize implementations.

#![warn(clippy::pedantic, clippy::restriction)]
// The only way I can see the enums changing would be changes to the variants themselves rather than
// addition of new variants. This means whether they non-exhaustive or not would not matter as the
// changes would be breaking regardless.
#![allow(
    clippy::blanket_clippy_restriction_lints,
    clippy::implicit_return,
    clippy::exhaustive_enums,
    clippy::decimal_literal_representation,
    clippy::non_ascii_literal,
    clippy::std_instead_of_core,
    clippy::missing_docs_in_private_items,
    clippy::std_instead_of_alloc,
    clippy::pub_use,
    clippy::single_char_lifetime_names
)]

use std::cmp::{Ord, Ordering, PartialOrd};
use std::fmt;

#[cfg(doc)]
mod example;
pub use bit_fields_macros::*;
#[cfg(doc)]
pub use example::ExampleBitField;

/// Exported error types.
mod errors;
pub use errors::*;

/// Trait used to define generic bit field functionality.
pub trait BitField {
    /// Compares whether `self` is equal to `other` ignoring undefined bits.
    fn equal(&self, other: &Self) -> bool;
}

/// Trait used for indexing into a bit field.
///
/// ```ignore
/// let bit_field = bit_fields::bitfield!(MyBitField,u8,{A:0,B:1,C:3,D:7});
/// let _a = bit_field.bit::<0>();
/// let _b = bit_field.bit::<1>();
/// let _c = bit_field.bit::<3>();
///
/// // You can index to unnamed bits like this.
/// let _ = bit_field.bit::<4>();
/// let _ = bit_field.bit::<5>();
/// let sixth = bit_field.bit::<6>();
/// println!("sixth: {}",sixth);
///
/// let d = bit_field.bit::<7>();
/// println!("d: {}",d);
/// ```
#[cfg(feature = "bit_index")]
pub trait BitIndex<T, const P: u8> {
    /// Gets a reference to a bit.
    fn bit(&self) -> Bit<'_, T, P>;
}
/// Trait used for mutable indexing into a bit field.
///
/// ```ignore
/// let bit_field = bit_fields::bitfield!(MyBitField,u8,{A:0,B:1,C:3,D:7});
/// let _a = bit_field.bit_mut::<0>();
/// let _b = bit_field.bit_mut::<1>();
/// let _c = bit_field.bit_mut::<3>();
///
/// // You can index to unnamed bits like this.
/// let _ = bit_field.bit_mut::<4>();
/// let _ = bit_field.bit_mut::<5>();
///
/// // We set the 6th bit to 0.
/// let mut sixth = bit_field.bit_mut::<6>();
/// sixth.off();
///
/// // We set the 7th bit to 1.
/// let mut d = bit_field.bit_mut::<7>();
/// d.on();
/// ```
#[cfg(feature = "bit_index")]
pub trait BitIndexMut<T, const P: u8> {
    /// Gets a mutable reference to a bit.
    fn bit_mut(&mut self) -> BitMut<'_, T, P>;
}

/// A type interface for a range of bits.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone)]
pub struct BitRange<'a, T, const START: u8, const END: u8>(pub &'a T);
/// A type interface for a range of bits.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
pub struct BitRangeMut<'a, T, const START: u8, const END: u8>(pub &'a mut T);

// std::fmt::Display
macro_rules! bit_range_display {
    ($x:ty) => {
        impl<const START: u8, const END: u8> fmt::Display for BitRange<'_, $x, START, END> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", <$x>::from(self))
            }
        }
    };
}
bit_range_display!(u128);
bit_range_display!(u64);
bit_range_display!(u32);
bit_range_display!(u16);
bit_range_display!(u8);
macro_rules! bit_range_mut_display {
    ($x:ty) => {
        impl<const START: u8, const END: u8> fmt::Display for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", <$x>::from(self))
            }
        }
    };
}
bit_range_mut_display!(u128);
bit_range_mut_display!(u64);
bit_range_mut_display!(u32);
bit_range_mut_display!(u16);
bit_range_mut_display!(u8);

// impl BitRange<..>
macro_rules! bit_range {
    ($x:ty,$mask:ident,$max:ident) => {
        impl<const START: u8, const END: u8> BitRange<'_, $x, START, END> {
            pub const MASK: $x = $mask::<START, END>();
            /// The maximum value this range can store
            pub const MAX: $x = $max::<START, END>();

            /// Returns the value of the bit range.
            #[must_use]
            #[inline]
            pub fn read(&self) -> $x {
                <$x>::from(self)
            }

            /// Conveniance alias for [`Self::MAX`].
            #[must_use]
            #[inline]
            pub const fn get_max(&self) -> $x {
                Self::MAX
            }
            /// Conveniance alias for [`Self::MASK`].
            #[must_use]
            #[inline]
            pub const fn get_mask(&self) -> $x {
                Self::MASK
            }
        }
    };
}
bit_range!(u128, mask_u128, max_u128);
bit_range!(u64, mask_u64, max_u64);
bit_range!(u32, mask_u32, max_u32);
bit_range!(u16, mask_u16, max_u16);
bit_range!(u8, mask_u8, max_u8);
macro_rules! bit_mut_range {
    ($x:ty,$mask:ident,$max:ident) => {
        impl<const START: u8, const END: u8> BitRangeMut<'_, $x, START, END> {
            pub const MASK: $x = $mask::<START, END>();
            /// The maximum value this range can store
            pub const MAX: $x = $max::<START, END>();

            /// Returns the value of the bit range.
            #[must_use]
            #[inline]
            pub fn read(&self) -> $x {
                <$x>::from(self)
            }

            /// Alias for [`Self::checked_assign`].
            ///
            /// # Errors
            ///
            /// When `x` is greater than the maximum storable value in `self`.
            // `x <= Self::MAX` guarantees `x << START` is safe.
            #[inline]
            pub fn write(&mut self, x: $x) -> Result<(), CheckedAssignError> {
                self.checked_assign(x)
            }

            /// Adds `x` to the value of the bit range.
            ///
            /// # Errors
            ///
            /// 1. When `x` is greater than the maximum value storable in the bit range.
            /// 2. When adding `x` to the value of the bit range would overflow.
            // `x <= Self::MAX` guarantees `x << START` is safe and `x <= Self::MAX - cur`
            // guarantees `self.data_mut() += shift` is safe.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn checked_add_assign(&mut self, x: $x) -> Result<(), CheckedAddAssignError> {
                if x <= Self::MAX {
                    let cur = (Self::MASK & *self.0) >> START;
                    if x <= Self::MAX - cur {
                        let shift = x << START;
                        *self.0 += shift;
                        Ok(())
                    } else {
                        Err(CheckedAddAssignError::Overflow)
                    }
                } else {
                    Err(CheckedAddAssignError::OutOfRange)
                }
            }

            /// Subtract `x` from the value of the bit range.
            ///
            /// # Errors
            ///
            /// 1. When `x` is greater than the maximum value storable in the bit range.
            /// 2. When subtracting `x` from the value of the bit range would underflow.
            // `x <= Self::MAX` guarantees `x << START` is safe and `x <= cur` guarantees
            // `self.data_mut() -= shift` is safe.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn checked_sub_assign(&mut self, x: $x) -> Result<(), CheckedSubAssignError> {
                if x <= Self::MAX {
                    let cur = (Self::MASK & *self.0) >> START;
                    if x <= cur {
                        let shift = x << START;
                        *self.0 -= shift;
                        Ok(())
                    } else {
                        Err(CheckedSubAssignError::Underflow)
                    }
                } else {
                    Err(CheckedSubAssignError::OutOfRange)
                }
            }

            /// Sets the bit range returning `Err(())` when the given `x` is not storable in the
            /// range.
            ///
            /// # Errors
            ///
            /// When `x` is greater than the maximum storable value in `self`.
            // `x <= Self::MAX` guarantees `x << START` is safe.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn checked_assign(&mut self, x: $x) -> Result<(), CheckedAssignError> {
                if x <= Self::MAX {
                    let shift = x << START;
                    *self.0 = shift | (*self.0 & !Self::MASK);
                    Ok(())
                } else {
                    Err(CheckedAssignError)
                }
            }
            /// Conveniance alias for [`Self::MAX`].
            #[must_use]
            #[inline]
            pub const fn get_max(&self) -> $x {
                Self::MAX
            }
            /// Conveniance alias for [`Self::MASK`].
            #[must_use]
            #[inline]
            pub const fn get_mask(&self) -> $x {
                Self::MASK
            }
        }
    };
}
bit_mut_range!(u128, mask_u128, max_u128);
bit_mut_range!(u64, mask_u64, max_u64);
bit_mut_range!(u32, mask_u32, max_u32);
bit_mut_range!(u16, mask_u16, max_u16);
bit_mut_range!(u8, mask_u8, max_u8);

// impl From<..> for BitRange<..>
macro_rules! bit_range_from {
    ($x:ty) => {
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time and would be immediately obvious. Thus it is safe to use arithmetic here.
        #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
        impl<const START: u8, const END: u8> From<&BitRange<'_, $x, START, END>> for $x {
            #[inline]
            fn from(this: &BitRange<'_, $x, START, END>) -> Self {
                let a = BitRange::<'_, $x, START, END>::MASK & *this.0;
                a >> START
            }
        }
    };
}

bit_range_from!(u128);
bit_range_from!(u64);
bit_range_from!(u32);
bit_range_from!(u16);
bit_range_from!(u8);
macro_rules! bit_range_mut_from {
    ($x:ty) => {
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time and would be immediately obvious. Thus it is safe to use arithmetic here.
        #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
        impl<const START: u8, const END: u8> From<&BitRangeMut<'_, $x, START, END>> for $x {
            #[inline]
            fn from(this: &BitRangeMut<'_, $x, START, END>) -> Self {
                let a = BitRangeMut::<'_, $x, START, END>::MASK & *this.0;
                a >> START
            }
        }
    };
}
bit_range_mut_from!(u128);
bit_range_mut_from!(u64);
bit_range_mut_from!(u32);
bit_range_mut_from!(u16);
bit_range_mut_from!(u8);

// impl std::cmp::PartialEq for BitRange<..>
macro_rules! bit_range_eq {
    ($x:ty) => {
        impl<const START: u8, const END: u8> PartialEq<$x> for BitRange<'_, $x, START, END> {
            #[inline]
            fn eq(&self, other: &$x) -> bool {
                let a = <$x>::from(self);
                a == *other
            }
        }
        impl<const START: u8, const END: u8> PartialEq for BitRange<'_, $x, START, END> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let a = <$x>::from(self);
                let b = <$x>::from(other);
                a == b
            }
        }
        impl<const START: u8, const END: u8> Eq for BitRange<'_, $x, START, END> {}
    };
}
bit_range_eq!(u128);
bit_range_eq!(u64);
bit_range_eq!(u32);
bit_range_eq!(u16);
bit_range_eq!(u8);
macro_rules! bit_range_mut_eq {
    ($x:ty) => {
        impl<const START: u8, const END: u8> PartialEq<$x> for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn eq(&self, other: &$x) -> bool {
                let a = <$x>::from(self);
                a == *other
            }
        }
        impl<const START: u8, const END: u8> PartialEq for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let a = <$x>::from(self);
                let b = <$x>::from(other);
                a == b
            }
        }
        impl<const START: u8, const END: u8> Eq for BitRangeMut<'_, $x, START, END> {}
    };
}
bit_range_mut_eq!(u128);
bit_range_mut_eq!(u64);
bit_range_mut_eq!(u32);
bit_range_mut_eq!(u16);
bit_range_mut_eq!(u8);

// impl std::cmp::Ord for BitRange<..>
macro_rules! bit_range_ord {
    ($x:ty) => {
        impl<const START: u8, const END: u8> PartialOrd<$x> for BitRange<'_, $x, START, END> {
            #[inline]
            fn partial_cmp(&self, other: &$x) -> Option<Ordering> {
                let a = <$x>::from(self);
                Some(a.cmp(other))
            }
        }
        impl<const START: u8, const END: u8> PartialOrd for BitRange<'_, $x, START, END> {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                let a = <$x>::from(self);
                let b = <$x>::from(other);
                Some(a.cmp(&b))
            }
        }
        impl<const START: u8, const END: u8> Ord for BitRange<'_, $x, START, END> {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }
    };
}
bit_range_ord!(u128);
bit_range_ord!(u64);
bit_range_ord!(u32);
bit_range_ord!(u16);
bit_range_ord!(u8);
macro_rules! bit_range_mut_ord {
    ($x:ty) => {
        impl<const START: u8, const END: u8> PartialOrd<$x> for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn partial_cmp(&self, other: &$x) -> Option<Ordering> {
                let a = <$x>::from(self);
                Some(a.cmp(other))
            }
        }
        impl<const START: u8, const END: u8> PartialOrd for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                let a = <$x>::from(self);
                let b = <$x>::from(other);
                Some(a.cmp(&b))
            }
        }
        impl<const START: u8, const END: u8> Ord for BitRangeMut<'_, $x, START, END> {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.partial_cmp(other).unwrap()
            }
        }
    };
}
bit_range_mut_ord!(u128);
bit_range_mut_ord!(u64);
bit_range_mut_ord!(u32);
bit_range_mut_ord!(u16);
bit_range_mut_ord!(u8);

/// A type interface for a single bit.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone)]
pub struct Bit<'a, T, const P: u8>(pub &'a T);
/// A type interface for a single bit.
#[allow(clippy::exhaustive_structs)]
#[derive(Debug)]
pub struct BitMut<'a, T, const P: u8>(pub &'a mut T);

// impl std::fmt::Display for Bit<..>
macro_rules! bit_display {
    ($x:ty) => {
        impl<const P: u8> fmt::Display for Bit<'_, $x, P> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", bool::from(self))
            }
        }
    };
}
bit_display!(u128);
bit_display!(u64);
bit_display!(u32);
bit_display!(u16);
bit_display!(u8);
macro_rules! bit_mut_display {
    ($x:ty) => {
        impl<const P: u8> fmt::Display for BitMut<'_, $x, P> {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", bool::from(self))
            }
        }
    };
}
bit_mut_display!(u128);
bit_mut_display!(u64);
bit_mut_display!(u32);
bit_mut_display!(u16);
bit_mut_display!(u8);

// impl Bit<..>
macro_rules! bit {
    ($x:ty) => {
        impl<const P: u8> Bit<'_, $x, P> {
            /// Returns the value of the bit.
            #[must_use]
            #[inline]
            pub fn read(&self) -> bool {
                bool::from(self)
            }
            /// Returns if the bit is 1.
            #[must_use]
            #[inline]
            pub fn is_on(&self) -> bool {
                bool::from(self)
            }
            /// Returns if the bit is 0.
            #[must_use]
            #[inline]
            pub fn is_off(&self) -> bool {
                !bool::from(self)
            }
        }
    };
}
bit!(u128);
bit!(u64);
bit!(u32);
bit!(u16);
bit!(u8);
macro_rules! bit_mut {
    ($x:ty) => {
        impl<const P: u8> BitMut<'_, $x, P> {
            /// Returns the value of the bit.
            #[must_use]
            #[inline]
            pub fn read(&self) -> bool {
                bool::from(self)
            }

            /// Alias for [`Self::set`].
            #[inline]
            pub fn write(&mut self, x: bool) {
                self.set(x);
            }

            /// Sets the value of the bit to 1.
            // These values are only evaluated at compile-time, thus a failure can only occur at
            // compile-time and would be immediately obvious. Thus it is safe to use arithmetic
            // here.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn on(&mut self) {
                *self.0 |= 1 << P;
            }

            /// Returns if the bit is 1.
            #[must_use]
            #[inline]
            pub fn is_on(&self) -> bool {
                bool::from(self)
            }

            /// Sets the value of the bit to 0.
            // These values are only evaluated at compile-time, thus a failure can only occur at
            // compile-time and would be immediately obvious. Thus it is safe to use arithmetic
            // here.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn off(&mut self) {
                *(self.0) &= !(1 << P);
            }

            /// Returns if the bit is 0.
            #[must_use]
            #[inline]
            pub fn is_off(&self) -> bool {
                !bool::from(self)
            }

            /// Flips the value of the bit.
            // These values are only evaluated at compile-time, thus a failure can only occur at
            // compile-time and would be immediately obvious. Thus it is safe to use arithmetic
            // here.
            #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
            #[inline]
            pub fn flip(&mut self) {
                *(self.0) ^= 1 << P;
            }

            /// Sets the value of the bit to `x as $x`.
            #[inline]
            pub fn set(&mut self, x: bool) {
                if x {
                    self.on()
                } else {
                    self.off()
                }
            }
        }
    };
}
bit_mut!(u128);
bit_mut!(u64);
bit_mut!(u32);
bit_mut!(u16);
bit_mut!(u8);

// impl From<..> for Bit<..>
macro_rules! bit_from {
    ($x:ty) => {
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time and would be immediately obvious. Thus it is safe to use arithmetic here.
        #[allow(clippy::integer_arithmetic, clippy::as_conversions, clippy::arithmetic)]
        impl<const P: u8> From<&Bit<'_, $x, P>> for bool {
            #[inline]
            fn from(this: &Bit<'_, $x, P>) -> Self {
                (*this.0 >> P) & (1 as $x).to_le() == (1 as $x).to_le()
            }
        }
    };
}
bit_from!(u128);
bit_from!(u64);
bit_from!(u32);
bit_from!(u16);
bit_from!(u8);
macro_rules! bit_mut_from {
    ($x:ty) => {
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time and would be immediately obvious. Thus it is safe to use arithmetic here.
        #[allow(clippy::integer_arithmetic, clippy::as_conversions, clippy::arithmetic)]
        impl<const P: u8> From<&BitMut<'_, $x, P>> for bool {
            #[inline]
            fn from(this: &BitMut<'_, $x, P>) -> Self {
                (*this.0 >> P) & (1 as $x).to_le() == (1 as $x).to_le()
            }
        }
    };
}
bit_mut_from!(u128);
bit_mut_from!(u64);
bit_mut_from!(u32);
bit_mut_from!(u16);
bit_mut_from!(u8);

// impl PartialEq<..> for Bit<..>
macro_rules! bit_eq {
    ($x:ty) => {
        impl<const P: u8> PartialEq for Bit<'_, $x, P> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let a = bool::from(self);
                let b = bool::from(other);
                a == b
            }
        }
        impl<const P: u8> PartialEq<bool> for Bit<'_, $x, P> {
            #[inline]
            fn eq(&self, other: &bool) -> bool {
                bool::from(self) == *other
            }
        }
        impl<const P: u8> Eq for Bit<'_, $x, P> {}
    };
}
bit_eq!(u128);
bit_eq!(u64);
bit_eq!(u32);
bit_eq!(u16);
bit_eq!(u8);
macro_rules! bit_mut_eq {
    ($x:ty) => {
        impl<const P: u8> PartialEq for BitMut<'_, $x, P> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let a = bool::from(self);
                let b = bool::from(other);
                a == b
            }
        }
        impl<const P: u8> PartialEq<bool> for BitMut<'_, $x, P> {
            #[inline]
            fn eq(&self, other: &bool) -> bool {
                bool::from(self) == *other
            }
        }
        impl<const P: u8> Eq for BitMut<'_, $x, P> {}
    };
}
bit_mut_eq!(u128);
bit_mut_eq!(u64);
bit_mut_eq!(u32);
bit_mut_eq!(u16);
bit_mut_eq!(u8);

/// Returns a value where in the binary representation all bits to the right of the x'th bit from
/// the left are 1.

macro_rules! shift {
    ($x:ident, $max:expr,$ty:path) => {{
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time and would be immediately obvious. Thus it is safe to use arithmetic here.
        #[allow(clippy::integer_arithmetic, clippy::arithmetic)]
        if $x == 0 {
            0
        } else if $x < $max {
            (1 << $x) - 1
        } else if $x == $max {
            $ty
        } else {
            // TODO Use `unreachable!()` here when panicking in const context is stabilized.
            0
        }
    }};
}

// Mask functions
macro_rules! mask_fn {
    ($f:ident,$x:ty,$y:path) => {
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time. This makes most fallible operations safe.
        #[allow(clippy::as_conversions)]
        const fn $f<const START: u8, const END: u8>() -> $x {
            let front = shift!(START, (std::mem::size_of::<$x>() * 8) as u8, $y);
            let back = shift!(END, (std::mem::size_of::<$x>() * 8) as u8, $y);
            !front & back
        }
    };
}
mask_fn!(mask_u128, u128, u128::MAX);
mask_fn!(mask_u64, u64, u64::MAX);
mask_fn!(mask_u32, u32, u32::MAX);
mask_fn!(mask_u16, u16, u16::MAX);
mask_fn!(mask_u8, u8, u8::MAX);

// Max functions
macro_rules! max_fn {
    ($f:ident,$x:ty) => {
        /// Returns maximum value storable in a range.
        ///
        /// We take `START`and `END` as const generics to ensure compile-time
        /// evaluation.
        // These values are only evaluated at compile-time, thus a failure can only occur at
        // compile-time. This makes most fallible operations safe.
        #[allow(clippy::integer_arithmetic, clippy::as_conversions, clippy::arithmetic)]
        const fn $f<const START: u8, const END: u8>() -> $x {
            match (2 as $x).overflowing_pow((END - START) as u32) {
                (_, true) => <$x>::MAX,
                (max, false) => max - 1,
            }
        }
    };
}
max_fn!(max_u128, u128);
max_fn!(max_u64, u64);
max_fn!(max_u32, u32);
max_fn!(max_u16, u16);
max_fn!(max_u8, u8);

#[allow(
    non_snake_case,
    clippy::dbg_macro,
    clippy::unwrap_used,
    clippy::as_conversions,
    clippy::shadow_unrelated
)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate as bit_fields;

    bitfield!(BitFieldu128, u128, {
        one: 0..1,
        two: 1..3,
        three: 3..6,
        four: 6..10,
        five: 10..15,
        six: 15..21,
        seven: 21..28,
        eight: 28..36,
        nine: 36..45,
        ten: 45..55,
        eleven: 55..66,
        twelve: 66..78,
        thirteen: 78..91,
        fourteen: 91..105,
        fifteen: 105..120,
        sixteen: 120,
        seventeen: 121,
        eighteen: 122,
        nineteen: 123,
        twenty: 124,
        twentyone: 125,
        twentytwo: 126,
        twentythree: 127,
    });
    bitfield!(BitFieldu64, u64, {
        one: 0..1,
        two: 1..3,
        three: 3..6,
        four: 6..10,
        five: 10..15,
        six: 15..21,
        seven: 21..28,
        eight: 28..36,
        nine: 36..45,
        ten: 45..55,
        eleven: 55,
        twelve: 56,
        thirteen: 57,
        fourteen: 58,
        fifteen: 59,
        sixteen: 60,
        seventeen: 61,
        eighteen: 62,
        nineteen: 63
    });
    bitfield!(BitFieldu32, u32, {
        one: 0..1,
        two: 1..3,
        three: 3..6,
        four: 6..10,
        five: 10..15,
        six: 15..21,
        seven: 21..28,
        eight: 28,
        nine: 29,
        ten: 30,
        eleven: 31
    });
    bitfield!(BitFieldu16, u16, {
        one: 0..1,
        two: 1..3,
        three: 3..6,
        four: 6..10,
        five: 10..15,
        six: 15
    });
    bitfield!(BitFieldu8, u8, {
        one: 0..1,
        two: 1..3,
        three: 3..6,
        four: 6,
        five: 7
    });

    use std::convert::TryFrom;

    use rand::Rng;

    bitfield!(
        GeneratedBitField,
        u32,
        {
            RANGE1:
            0..1,
            SSE:
            2,
            SSE1:
            3,
            RANGE2:
            4..6,
            SSE2:
            9,
            SSE3:
            10,
            RANGE3:
            12..15,
            SSE4:
            18
        }
    );

    #[test]
    fn display() {
        let field_u16 = BitFieldu16(0b1010_1110_0101_0111);
        let field_u8 = BitFieldu8(0b1010_1110);
        #[rustfmt::skip]
        assert_eq!(field_u16.to_string(),"\
            ┌───────┬─────────────┬─────────────┬─────────────┬─────────────┬─────────────┬───────┐\n\
            │ \x1b[1mBit/s\x1b[0m │      00..01 │      01..03 │      03..06 │      06..10 │      10..15 │    15 │\n\
            ├───────┼─────────────┼─────────────┼─────────────┼─────────────┼─────────────┼───────┤\n\
            │ \x1b[1mDesc\x1b[0m  │         one │         two │       three │        four │        five │   six │\n\
            ├───────┼─────────────┼─────────────┼─────────────┼─────────────┼─────────────┼───────┤\n\
            │ \x1b[1mValue\x1b[0m │           1 │           3 │           2 │           9 │          11 │  true │\n\
            └───────┴─────────────┴─────────────┴─────────────┴─────────────┴─────────────┴───────┘\n\
        ");
        #[rustfmt::skip]
        assert_eq!(field_u8.to_string(),"\
            ┌───────┬─────────────┬─────────────┬─────────────┬───────┬───────┐\n\
            │ \x1b[1mBit/s\x1b[0m │      00..01 │      01..03 │      03..06 │    06 │    07 │\n\
            ├───────┼─────────────┼─────────────┼─────────────┼───────┼───────┤\n\
            │ \x1b[1mDesc\x1b[0m  │         one │         two │       three │  four │  five │\n\
            ├───────┼─────────────┼─────────────┼─────────────┼───────┼───────┤\n\
            │ \x1b[1mValue\x1b[0m │           0 │           3 │           5 │ false │  true │\n\
            └───────┴─────────────┴─────────────┴─────────────┴───────┴───────┘\n\
        ");
    }
    // Testing bit field sizes
    #[test]
    fn size() {
        use std::mem::size_of;
        assert_eq!(size_of::<BitFieldu128>(), size_of::<u128>());
        assert_eq!(size_of::<BitFieldu64>(), size_of::<u64>());
        assert_eq!(size_of::<BitFieldu32>(), size_of::<u32>());
        assert_eq!(size_of::<BitFieldu16>(), size_of::<u16>());
        assert_eq!(size_of::<BitFieldu8>(), size_of::<u8>());
    }
    // Testing masks work
    #[test]
    fn mask() {
        // These top level checks exists to communicate to code coverage that this function is
        // covered
        assert_eq!(mask_u128::<0, 0>(), 0);
        assert_eq!(mask_u64::<0, 0>(), 0);
        assert_eq!(mask_u32::<0, 0>(), 0);
        assert_eq!(mask_u16::<0, 0>(), 0);
        assert_eq!(mask_u8::<0, 0>(), 0);
        // u128
        assert_eq!(
            mask_u128::<0, 128>(),
            0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff
        );
        assert_eq!(
            mask_u128::<0, 64>(),
            0x0000_0000_0000_0000_ffff_ffff_ffff_ffff
        );
        assert_eq!(
            mask_u128::<64, 128>(),
            0xffff_ffff_ffff_ffff_0000_0000_0000_0000
        );
        // u64
        assert_eq!(mask_u64::<0, 64>(), 0xffff_ffff_ffff_ffff);
        assert_eq!(mask_u64::<0, 32>(), 0x0000_0000_ffff_ffff);
        assert_eq!(mask_u64::<32, 64>(), 0xffff_ffff_0000_0000);
        assert_eq!(mask_u64::<4, 60>(), 0x0fff_ffff_ffff_fff0);
        assert_eq!(mask_u64::<8, 56>(), 0x00ff_ffff_ffff_ff00);
        assert_eq!(mask_u64::<12, 52>(), 0x000f_ffff_ffff_f000);
        assert_eq!(mask_u64::<16, 48>(), 0x0000_ffff_ffff_0000);
        assert_eq!(mask_u64::<20, 44>(), 0x0000_0fff_fff0_0000);
        assert_eq!(mask_u64::<24, 40>(), 0x0000_00ff_ff00_0000);
        assert_eq!(mask_u64::<28, 36>(), 0x0000_000f_f000_0000);
        assert_eq!(
            mask_u64::<30, 34>(),
            0b0000_0000_0000_0000_0000_0000_0000_0011_1100_0000_0000_0000_0000_0000_0000_0000
        );
        assert_eq!(
            mask_u64::<31, 33>(),
            0b0000_0000_0000_0000_0000_0000_0000_0001_1000_0000_0000_0000_0000_0000_0000_0000
        );
        // u32
        assert_eq!(mask_u32::<0, 32>(), 0xffff_ffff);
        assert_eq!(mask_u32::<0, 16>(), 0x0000_ffff);
        assert_eq!(mask_u32::<16, 32>(), 0xffff_0000);
        assert_eq!(mask_u32::<4, 28>(), 0x0fff_fff0);
        assert_eq!(mask_u32::<8, 24>(), 0x00ff_ff00);
        assert_eq!(mask_u32::<12, 20>(), 0x000f_f000);
        assert_eq!(
            mask_u32::<14, 18>(),
            0b0000_0000_0000_0011_1100_0000_0000_0000
        );
        assert_eq!(
            mask_u32::<15, 17>(),
            0b0000_0000_0000_0001_1000_0000_0000_0000
        );
        // u16
        assert_eq!(mask_u16::<0, 16>(), 0xffff);
        assert_eq!(mask_u16::<0, 8>(), 0x00ff);
        assert_eq!(mask_u16::<8, 16>(), 0xff00);
        assert_eq!(mask_u16::<4, 12>(), 0x0ff0);
        assert_eq!(mask_u16::<6, 10>(), 0b0000_0011_1100_0000);
        assert_eq!(mask_u16::<7, 9>(), 0b0000_0001_1000_0000);
        // u8
        assert_eq!(mask_u8::<0, 8>(), 0b1111_1111);
        assert_eq!(mask_u8::<0, 4>(), 0b0000_1111);
        assert_eq!(mask_u8::<4, 8>(), 0b1111_0000);
        assert_eq!(mask_u8::<2, 6>(), 0b0011_1100);
        assert_eq!(mask_u8::<3, 5>(), 0b0001_1000);
    }
    #[test]
    fn type_max() {
        // u128
        assert_eq!(BitRange::<u128, 0, 1>::MAX, 1);
        assert_eq!(BitRange::<u128, 1, 3>::MAX, 3);
        assert_eq!(BitRange::<u128, 3, 6>::MAX, 7);
        assert_eq!(BitRange::<u128, 6, 10>::MAX, 15);
        assert_eq!(BitRange::<u128, 10, 15>::MAX, 31);
        assert_eq!(BitRange::<u128, 15, 21>::MAX, 63);
        assert_eq!(BitRange::<u128, 21, 28>::MAX, 127);
        assert_eq!(BitRange::<u128, 28, 36>::MAX, 255);
        assert_eq!(BitRange::<u128, 36, 45>::MAX, 511);
        assert_eq!(BitRange::<u128, 45, 55>::MAX, 1023);
        assert_eq!(BitRange::<u128, 55, 66>::MAX, 2047);
        assert_eq!(BitRange::<u128, 66, 78>::MAX, 4095);
        assert_eq!(BitRange::<u128, 78, 91>::MAX, 8191);
        assert_eq!(BitRange::<u128, 91, 105>::MAX, 16383);
        assert_eq!(BitRange::<u128, 105, 120>::MAX, 32767);

        // u64
        assert_eq!(BitRange::<u64, 0, 1>::MAX, 1);
        assert_eq!(BitRange::<u64, 1, 3>::MAX, 3);
        assert_eq!(BitRange::<u64, 3, 6>::MAX, 7);
        assert_eq!(BitRange::<u64, 6, 10>::MAX, 15);
        assert_eq!(BitRange::<u64, 10, 15>::MAX, 31);
        assert_eq!(BitRange::<u64, 15, 21>::MAX, 63);
        assert_eq!(BitRange::<u64, 21, 28>::MAX, 127);
        assert_eq!(BitRange::<u64, 28, 36>::MAX, 255);
        assert_eq!(BitRange::<u64, 36, 45>::MAX, 511);
        assert_eq!(BitRange::<u64, 45, 55>::MAX, 1023);

        // u32
        assert_eq!(BitRange::<u32, 0, 1>::MAX, 1);
        assert_eq!(BitRange::<u32, 1, 3>::MAX, 3);
        assert_eq!(BitRange::<u32, 3, 6>::MAX, 7);
        assert_eq!(BitRange::<u32, 6, 10>::MAX, 15);
        assert_eq!(BitRange::<u32, 10, 15>::MAX, 31);
        assert_eq!(BitRange::<u32, 15, 21>::MAX, 63);
        assert_eq!(BitRange::<u32, 21, 28>::MAX, 127);

        // u16
        assert_eq!(BitRange::<u16, 0, 1>::MAX, 1);
        assert_eq!(BitRange::<u16, 1, 3>::MAX, 3);
        assert_eq!(BitRange::<u16, 3, 6>::MAX, 7);
        assert_eq!(BitRange::<u16, 6, 10>::MAX, 15);
        assert_eq!(BitRange::<u16, 10, 15>::MAX, 31);

        assert_eq!(BitRange::<u16, 0, 16>::MAX, 65535);
        assert_eq!(BitRange::<u16, 0, 8>::MAX, 255);
        assert_eq!(BitRange::<u16, 8, 16>::MAX, 255);
        assert_eq!(BitRange::<u16, 4, 12>::MAX, 255);
        assert_eq!(BitRange::<u16, 6, 10>::MAX, 15);
        assert_eq!(BitRange::<u16, 7, 9>::MAX, 3);

        // u8
        assert_eq!(BitRange::<u8, 0, 1>::MAX, 1);
        assert_eq!(BitRange::<u8, 1, 3>::MAX, 3);
        assert_eq!(BitRange::<u8, 3, 6>::MAX, 7);

        assert_eq!(BitRange::<u8, 0, 8>::MAX, 255);
        assert_eq!(BitRange::<u8, 0, 4>::MAX, 15);
        assert_eq!(BitRange::<u8, 4, 8>::MAX, 15);
        assert_eq!(BitRange::<u8, 2, 6>::MAX, 15);
        assert_eq!(BitRange::<u8, 3, 5>::MAX, 3);
    }
    #[test]
    fn value_max() {
        let field_u128: BitFieldu128 = BitFieldu128(0);
        let field_u64: BitFieldu64 = BitFieldu64(0);
        let field_u32: BitFieldu32 = BitFieldu32(0);
        let field_u16: BitFieldu16 = BitFieldu16(0);
        let field_u8: BitFieldu8 = BitFieldu8(0);

        // u128
        assert_eq!(field_u128.one().get_max(), 1);
        assert_eq!(field_u128.two().get_max(), 3);
        assert_eq!(field_u128.three().get_max(), 7);
        assert_eq!(field_u128.four().get_max(), 15);
        assert_eq!(field_u128.five().get_max(), 31);
        assert_eq!(field_u128.six().get_max(), 63);
        assert_eq!(field_u128.seven().get_max(), 127);
        assert_eq!(field_u128.eight().get_max(), 255);
        assert_eq!(field_u128.nine().get_max(), 511);
        assert_eq!(field_u128.ten().get_max(), 1023);
        assert_eq!(field_u128.eleven().get_max(), 2047);
        assert_eq!(field_u128.twelve().get_max(), 4095);
        assert_eq!(field_u128.thirteen().get_max(), 8191);
        assert_eq!(field_u128.fourteen().get_max(), 16383);
        assert_eq!(field_u128.fifteen().get_max(), 32767);
        // u64
        assert_eq!(field_u64.one().get_max(), 1);
        assert_eq!(field_u64.two().get_max(), 3);
        assert_eq!(field_u64.three().get_max(), 7);
        assert_eq!(field_u64.four().get_max(), 15);
        assert_eq!(field_u64.five().get_max(), 31);
        assert_eq!(field_u64.six().get_max(), 63);
        assert_eq!(field_u64.seven().get_max(), 127);
        assert_eq!(field_u64.eight().get_max(), 255);
        assert_eq!(field_u64.nine().get_max(), 511);
        assert_eq!(field_u64.ten().get_max(), 1023);
        // u32
        assert_eq!(field_u32.one().get_max(), 1);
        assert_eq!(field_u32.two().get_max(), 3);
        assert_eq!(field_u32.three().get_max(), 7);
        assert_eq!(field_u32.four().get_max(), 15);
        assert_eq!(field_u32.five().get_max(), 31);
        assert_eq!(field_u32.six().get_max(), 63);
        assert_eq!(field_u32.seven().get_max(), 127);
        // u16
        assert_eq!(field_u16.one().get_max(), 1);
        assert_eq!(field_u16.two().get_max(), 3);
        assert_eq!(field_u16.three().get_max(), 7);
        assert_eq!(field_u16.four().get_max(), 15);
        assert_eq!(field_u16.five().get_max(), 31);
        // u8
        assert_eq!(field_u8.one().get_max(), 1);
        assert_eq!(field_u8.two().get_max(), 3);
        assert_eq!(field_u8.three().get_max(), 7);
    }
    #[test]
    fn access() {
        let bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);
    }
    #[test]
    fn flip() {
        let mut bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);

        bitfield.SSE_mut().flip();
        bitfield.SSE1_mut().flip();
        bitfield.SSE2_mut().flip();
        bitfield.SSE3_mut().flip();
        bitfield.SSE4_mut().flip();

        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), false);
        assert_eq!(bitfield.SSE1(), false);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), false);
        assert_eq!(bitfield.SSE3(), true);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), true);
    }
    #[test]
    fn set() {
        let mut bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);

        bitfield.SSE_mut().set(false);
        bitfield.SSE1_mut().set(false);
        bitfield.SSE2_mut().set(true);
        bitfield.SSE3_mut().set(true);
        bitfield.SSE4_mut().set(false);

        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), false);
        assert_eq!(bitfield.SSE1(), false);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), true);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);
    }
    #[test]
    fn on_off() {
        let mut bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);

        bitfield.SSE_mut().off();
        bitfield.SSE1_mut().on();
        bitfield.SSE2_mut().on();
        bitfield.SSE4_mut().on();

        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), false);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), true);
    }

    #[allow(clippy::trivially_copy_pass_by_ref)]
    fn check(bitfield: &GeneratedBitField, r1: u32, r2: u32, r3: u32) {
        assert_eq!(bitfield.RANGE1(), r1, "{}", bitfield.RANGE1().read());
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), r2, "{}", bitfield.RANGE2().read());
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), r3, "{}", bitfield.RANGE3().read());
        assert_eq!(bitfield.SSE4(), false);
    }

    #[test]
    fn checked_add_assign() {
        let mut bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);

        assert_eq!(bitfield.RANGE1_mut().checked_add_assign(1), Ok(()));
        assert_eq!(bitfield.RANGE1(), 1);

        assert_eq!(
            bitfield.RANGE1_mut().checked_add_assign(1),
            Err(CheckedAddAssignError::Overflow)
        );
        assert_eq!(bitfield.RANGE1(), 1);

        assert_eq!(
            bitfield.RANGE2_mut().checked_add_assign(1),
            Err(CheckedAddAssignError::Overflow)
        );
        assert_eq!(bitfield.RANGE1(), 1);

        assert_eq!(bitfield.RANGE3_mut().checked_add_assign(2), Ok(()));
        assert_eq!(bitfield.RANGE3(), 7);

        assert_eq!(
            bitfield.RANGE3_mut().checked_add_assign(1),
            Err(CheckedAddAssignError::Overflow)
        );
        assert_eq!(bitfield.RANGE3(), 7);

        assert_eq!(
            bitfield.RANGE3_mut().checked_add_assign(8),
            Err(CheckedAddAssignError::OutOfRange)
        );
        assert_eq!(bitfield.RANGE3(), 7);

        // We check all values are as expected at tend (we do this to ensure no operation overflow)
        assert_eq!(bitfield.RANGE1(), 1);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 7);
        assert_eq!(bitfield.SSE4(), false);
    }
    const ITERATIONS: usize = 100_000;
    const MAX: u32 = 100;
    #[test]
    fn checked_sub_assign() {
        let mut bitfield = GeneratedBitField::from(23548);
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 3);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);

        assert_eq!(
            bitfield.RANGE1_mut().checked_sub_assign(1),
            Err(CheckedSubAssignError::Underflow)
        );
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(
            bitfield.RANGE1_mut().checked_sub_assign(2),
            Err(CheckedSubAssignError::OutOfRange)
        );
        assert_eq!(bitfield.RANGE1(), 0);

        assert_eq!(bitfield.RANGE2_mut().checked_sub_assign(1), Ok(()));
        assert_eq!(bitfield.RANGE2(), 2);

        // We check all values are as expected at tend (we do this to ensure no operation overflow)
        assert_eq!(bitfield.RANGE1(), 0);
        assert_eq!(bitfield.SSE(), true);
        assert_eq!(bitfield.SSE1(), true);
        assert_eq!(bitfield.RANGE2(), 2);
        assert_eq!(bitfield.SSE2(), true);
        assert_eq!(bitfield.SSE3(), false);
        assert_eq!(bitfield.RANGE3(), 5);
        assert_eq!(bitfield.SSE4(), false);
    }
    #[test]
    fn add_sub() {
        let mut bitfield = GeneratedBitField::from(23548);

        let (mut range1, mut range2, mut range3) = (0, 3, 5);
        check(&bitfield, range1, range2, range3);

        let mut rng = rand::thread_rng();
        // Randomly add and sub to `RANGE1`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            if rng.gen() {
                dbg!(next);
                range1 += bitfield
                    .RANGE1_mut()
                    .checked_add_assign(next)
                    .map_or(0, |_| next);
            } else {
                dbg!(next);
                range1 -= bitfield
                    .RANGE1_mut()
                    .checked_sub_assign(next)
                    .map_or(0, |_| next);
            }
            check(&bitfield, range1, range2, range3);
        }
        // Randomly add and sub to `RANGE2`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            if rng.gen() {
                dbg!(next);
                range2 += bitfield
                    .RANGE2_mut()
                    .checked_add_assign(next)
                    .map_or(0, |_| next);
            } else {
                dbg!(next);
                range2 -= bitfield
                    .RANGE2_mut()
                    .checked_sub_assign(next)
                    .map_or(0, |_| next);
            }
            check(&bitfield, range1, range2, range3);
        }
        // Randomly add and sub to `RANGE3`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            if rng.gen() {
                dbg!(next);
                range3 += bitfield
                    .RANGE3_mut()
                    .checked_add_assign(next)
                    .map_or(0, |_| next);
            } else {
                dbg!(next);
                range3 -= bitfield
                    .RANGE3_mut()
                    .checked_sub_assign(next)
                    .map_or(0, |_| next);
            }
            check(&bitfield, range1, range2, range3);
        }
    }
    #[test]
    fn checked_assign() {
        let mut bitfield = GeneratedBitField::from(23548);

        let (mut range1, mut range2, mut range3) = (0, 3, 5);
        check(&bitfield, range1, range2, range3);

        let mut rng = rand::thread_rng();
        // Randomly assign to `range1`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            dbg!(next);
            range1 = match bitfield.RANGE1_mut().checked_assign(next) {
                Ok(()) => next,
                Err(CheckedAssignError) => range1,
            };
            check(&bitfield, range1, range2, range3);
        }
        // Randomly assign to `RANGE2`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            dbg!(next);
            range2 = match bitfield.RANGE2_mut().checked_assign(next) {
                Ok(()) => next,
                Err(CheckedAssignError) => range2,
            };
            check(&bitfield, range1, range2, range3);
        }
        // Randomly assign to `RANGE3`
        for _ in 0..ITERATIONS {
            let next = rng.gen_range(0..MAX);
            dbg!(next);
            range3 = match bitfield.RANGE3_mut().checked_assign(next) {
                Ok(()) => next,
                Err(CheckedAssignError) => range3,
            };
            check(&bitfield, range1, range2, range3);
        }
    }
    #[test]
    fn conversion() {
        use std::collections::{HashMap, HashSet};

        let mut rng = rand::thread_rng();

        let bitfield_u8_before = BitFieldu8::from(rng.gen::<u8>());
        let (set, map) = <(HashSet<String>, HashMap<String, u8>)>::from(&bitfield_u8_before);
        let bitfield_u8_after = BitFieldu8::try_from((set, map)).unwrap();
        assert_eq!(bitfield_u8_before, bitfield_u8_after);

        let bitfield_u16_before = BitFieldu16::from(rng.gen::<u16>());
        let (set, map) = <(HashSet<String>, HashMap<String, u16>)>::from(&bitfield_u16_before);
        let bitfield_u16_after = BitFieldu16::try_from((set, map)).unwrap();
        assert_eq!(bitfield_u16_before, bitfield_u16_after);

        let bitfield_u32_before = BitFieldu32::from(rng.gen::<u32>());
        let (set, map) = <(HashSet<String>, HashMap<String, u32>)>::from(&bitfield_u32_before);
        let bitfield_u32_after = BitFieldu32::try_from((set, map)).unwrap();
        assert_eq!(bitfield_u32_before, bitfield_u32_after);

        let bitfield_u64_before = BitFieldu64::from(rng.gen::<u64>());
        let (set, map) = <(HashSet<String>, HashMap<String, u64>)>::from(&bitfield_u64_before);
        let bitfield_u64_after = BitFieldu64::try_from((set, map)).unwrap();
        assert_eq!(bitfield_u64_before, bitfield_u64_after);

        let bitfield_u128_before = BitFieldu128::from(rng.gen::<u128>());
        let (set, map) = <(HashSet<String>, HashMap<String, u128>)>::from(&bitfield_u128_before);
        let bitfield_u128_after = BitFieldu128::try_from((set, map)).unwrap();
        assert_eq!(bitfield_u128_before, bitfield_u128_after);
    }
    #[test]
    fn serialize() {
        let mut rng = rand::thread_rng();

        let bitfield_u8_before = BitFieldu8::from(rng.gen::<u8>());
        let serialized = serde_json::to_vec(&bitfield_u8_before).unwrap();
        let bitfield_u8_after = serde_json::from_slice::<BitFieldu8>(&serialized).unwrap();
        assert_eq!(bitfield_u8_before, bitfield_u8_after);

        let bitfield_u16_before = BitFieldu16::from(rng.gen::<u16>());
        let serialized = serde_json::to_vec(&bitfield_u16_before).unwrap();
        let bitfield_u16_after = serde_json::from_slice::<BitFieldu16>(&serialized).unwrap();
        assert_eq!(bitfield_u16_before, bitfield_u16_after);

        let bitfield_u32_before = BitFieldu32::from(rng.gen::<u32>());
        let serialized = serde_json::to_vec(&bitfield_u32_before).unwrap();
        let bitfield_u32_after = serde_json::from_slice::<BitFieldu32>(&serialized).unwrap();
        assert_eq!(bitfield_u32_before, bitfield_u32_after);

        let bitfield_u64_before = BitFieldu64::from(rng.gen::<u64>());
        let serialized = serde_json::to_vec(&bitfield_u64_before).unwrap();
        let bitfield_u64_after = serde_json::from_slice::<BitFieldu64>(&serialized).unwrap();
        assert_eq!(bitfield_u64_before, bitfield_u64_after);

        let bitfield_u128_before = BitFieldu128::from(rng.gen::<u128>());
        let serialized = serde_json::to_vec(&bitfield_u128_before).unwrap();
        let bitfield_u128_after = serde_json::from_slice::<BitFieldu128>(&serialized).unwrap();
        assert_eq!(bitfield_u128_before, bitfield_u128_after);
    }
}
