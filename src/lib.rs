#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]
#![allow(clippy::manual_range_contains)]

#[cfg(all(feature = "anchor", feature = "anyhow_error"))]
compile_error!(
    "features `crate/anchor` and `crate/anyhow_error` are mutually exclusive"
);

pub mod f64;
pub mod u192_decimal;

#[cfg(feature = "anchor")]
use anchor_lang::prelude::*;
#[cfg(feature = "anyhow_error")]
pub use anyhow::Result;
use std::fmt;
pub use u192_decimal::Decimal;

mod custom_u192 {
    use uint::construct_uint;

    // U192 with 192 bits consisting of 3 x 64-bit words
    construct_uint! {
        pub struct U192(3);
    }
}

pub use custom_u192::U192;

#[cfg_attr(feature = "anchor", error_code)]
#[cfg_attr(feature = "anyhow_error", derive(thiserror::Error, Debug))]
#[derive(PartialEq, Eq)]
pub enum DecimalError {
    MathOverflow,
}

pub trait TrySub<RHS>: Sized {
    fn try_sub(&self, rhs: RHS) -> Result<Self>;
}

pub trait TryAdd<RHS>: Sized {
    fn try_add(&self, rhs: RHS) -> Result<Self>;
}

pub trait TryDiv<RHS>: Sized {
    fn try_div(&self, rhs: RHS) -> Result<Self>;
}

pub trait TryMul<RHS>: Sized {
    fn try_mul(&self, rhs: RHS) -> Result<Self>;
}

pub trait TrySqrt: Sized {
    fn try_sqrt(&self) -> Result<Self>;
}

pub trait TryPow<RHS>: Sized {
    /// self^rhs
    fn try_pow(&self, rhs: RHS) -> Result<Self>;
}

pub trait TryLn: Sized {
    fn try_ln(&self) -> Result<Self>;
}

impl<T: TryMul<T> + From<u64> + Clone> TryPow<u64> for T {
    /// Calculates base^exp
    fn try_pow(&self, mut exp: u64) -> Result<Self> {
        let mut base = self.clone();
        let mut ret = if exp % 2 != 0 {
            base.clone()
        } else {
            Self::from(1)
        };

        loop {
            exp /= 2;
            if exp == 0 {
                break;
            }

            base = base.try_mul(base.clone())?;

            if exp % 2 != 0 {
                ret = ret.try_mul(base.clone())?;
            }
        }

        Ok(ret)
    }
}

pub trait ScaledVal {
    fn to_scaled_val(&self) -> Result<u128>;
    fn from_scaled_val(scaled_val: u128) -> Self;
}

pub trait AlmostEq: ScaledVal + TrySub<Self> + Ord + Clone {
    /// If the difference between self and other is less than 10^(dec_places -
    /// precision), return true.
    ///
    /// # Example
    /// If we have 18 decimal places, than having precision of 6 would mean that
    /// any difference beyond 12th dec place is considered as equal.
    fn almost_eq(&self, other: &Self, precision: u32) -> bool {
        let precision = Self::from_scaled_val(10u128.pow(precision));
        match self.cmp(other) {
            std::cmp::Ordering::Equal => true,
            std::cmp::Ordering::Less => {
                other.try_sub(self.clone()).unwrap() < precision
            }
            std::cmp::Ordering::Greater => {
                self.try_sub(other.clone()).unwrap() < precision
            }
        }
    }
}

pub trait TryRound<T> {
    fn try_floor(&self) -> Result<T>;
    fn try_ceil(&self) -> Result<T>;
    fn try_round(&self) -> Result<T>;
}

/// Approximate the nth root of a number using Newton's method
/// https://en.wikipedia.org/wiki/Newton%27s_method
/// NOTE: this function is private because its accurate range and precision
/// have not been established.
///
/// Based on https://docs.rs/spl-math/0.1.0/spl_math/precise_number/struct.PreciseNumber.html#method.sqrt
fn newtonian_root_approximation<
    'a,
    T: PartialEq
        + Clone
        + TryMul<T>
        + AlmostEq
        + TryPow<u64>
        + TryAdd<T>
        + TryDiv<T>
        + TrySub<T>
        + From<u64>
        + TryRound<u64>,
>(
    base: T,
    root: T,
    mut guess: T,
) -> Result<T> {
    const MAX_APPROXIMATION_ITERATIONS: u128 = 100;

    let zero = T::from(0u64);
    if base == zero {
        return Ok(zero);
    }
    if root == zero {
        return Err(yield_error());
    }
    let one = T::from(1u64);
    let root_minus_one = root.try_sub(one)?;
    let root_minus_one_whole = root_minus_one.try_round()?;
    let mut last_guess = guess.clone();
    for _ in 0..MAX_APPROXIMATION_ITERATIONS {
        // x_k+1 = ((n - 1) * x_k + A / (x_k ^ (n - 1))) / n
        let first_term = root_minus_one.clone().try_mul(guess.clone())?;
        let power = guess.clone().try_pow(root_minus_one_whole as u64);
        let second_term = match power {
            Ok(num) => base.clone().try_div(num)?,
            Err(_) => T::from(0u64),
        };
        guess = first_term.try_add(second_term)?.try_div(root.clone())?;
        // the source uses precision of 2 places, but we originally used 3
        // places and want to keep the same precision as we tested our
        // programs with
        if last_guess.almost_eq(&guess, 3) {
            break;
        } else {
            last_guess = guess.clone();
        }
    }

    Ok(guess)
}

#[cfg(feature = "anyhow_error")]
impl fmt::Display for DecimalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "decimal crate math error ({:?})", self)
    }
}

#[cfg(feature = "anyhow_error")]
fn yield_error() -> anyhow::Error {
    DecimalError::MathOverflow.into()
}

#[cfg(feature = "anchor")]
fn yield_error() -> anchor_lang::prelude::Error {
    DecimalError::MathOverflow.into()
}
