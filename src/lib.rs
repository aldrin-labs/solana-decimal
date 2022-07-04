pub mod u192_decimal;
pub mod u320_decimal;

use anchor_lang::prelude::*;
use std::{convert::TryFrom, fmt};
pub use u192_decimal::Decimal;
pub use u320_decimal::LargeDecimal;

mod custom_u192 {
    use uint::construct_uint;

    // U192 with 192 bits consisting of 3 x 64-bit words
    construct_uint! {
        pub struct U192(3);
    }
}

mod custom_u320 {
    use uint::construct_uint;

    construct_uint! {
        pub struct U320(5);
    }
}

pub use custom_u192::U192;
pub use custom_u320::U320;

#[error_code]
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

pub trait AlmostEq {
    fn almost_eq(&self, other: &Self) -> bool;
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
        return Err(error!(DecimalError::MathOverflow));
    }
    let one = T::from(1u64);
    let root_minus_one = root.clone().try_sub(one)?;
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
        if last_guess.almost_eq(&guess) {
            break;
        } else {
            last_guess = guess.clone();
        }
    }

    Ok(guess)
}
