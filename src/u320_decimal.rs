//! Math for preserving precision of token amounts which are limited
//! by the SPL Token program to be at most u64::MAX.
//!
//! Decimals are internally scaled by an identity (10^6) to preserve
//! precision up to 6 decimal places. Decimals are sized to support
//! both serialization and precise math for the full range of
//! unsigned 64-bit integers. The underlying representation is a u320. This
//! enables arithmetic ops at the high range of u64.

#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]
#![allow(clippy::manual_range_contains)]

use super::*;
use std::convert::TryFrom;

pub mod consts {
    /// Scale of precision.
    pub const SCALE: usize = 6;

    /// Identity
    pub const IDENTITY: u64 = 1_000_000;

    pub const TWO_IDENTITIES: u64 = IDENTITY * 2;

    pub const HALF_IDENTITY: u64 = IDENTITY / 2;
}

/// Large decimal values, precise to 6 digits
#[derive(Clone, Debug, Default, PartialEq, PartialOrd, Eq, Ord)]
pub struct LargeDecimal(pub U320);

impl LargeDecimal {
    pub fn one() -> Self {
        Self(Self::identity())
    }

    pub fn two() -> Self {
        Self(U320::from(consts::TWO_IDENTITIES))
    }

    pub fn zero() -> Self {
        Self(U320::zero())
    }

    // OPTIMIZE: use const slice when fixed in BPF toolchain
    fn identity() -> U320 {
        U320::from(consts::IDENTITY)
    }

    // OPTIMIZE: use const slice when fixed in BPF toolchain
    fn half_identity() -> U320 {
        U320::from(consts::HALF_IDENTITY)
    }

    /// Return raw scaled value if it fits within u128
    #[allow(clippy::wrong_self_convention)]
    pub fn to_scaled_val(&self) -> Result<u128> {
        Ok(u128::try_from(self.0).map_err(|_| DecimalError::MathOverflow)?)
    }

    pub fn from_scaled_val(scaled_val: u128) -> Self {
        Self(U320::from(scaled_val))
    }
}

impl TryRound<u64> for LargeDecimal {
    fn try_round(&self) -> Result<u64> {
        let rounded_val = Self::half_identity()
            .checked_add(self.0)
            .ok_or(DecimalError::MathOverflow)?
            .checked_div(Self::identity())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(rounded_val)
            .map_err(|_| DecimalError::MathOverflow)?)
    }

    fn try_ceil(&self) -> Result<u64> {
        let ceil_val = Self::identity()
            .checked_sub(U320::from(1u64))
            .ok_or(DecimalError::MathOverflow)?
            .checked_add(self.0)
            .ok_or(DecimalError::MathOverflow)?
            .checked_div(Self::identity())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(ceil_val).map_err(|_| DecimalError::MathOverflow)?)
    }

    fn try_floor(&self) -> Result<u64> {
        let ceil_val = self
            .0
            .checked_div(Self::identity())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(ceil_val).map_err(|_| DecimalError::MathOverflow)?)
    }
}

impl AlmostEq for LargeDecimal {
    /// The precision is 15 decimal places
    fn almost_eq(&self, other: &Self) -> bool {
        let precision = Self::from_scaled_val(1000);
        match self.cmp(&other) {
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

impl fmt::Display for LargeDecimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut scaled_val = self.0.to_string();
        if scaled_val.len() <= consts::SCALE {
            scaled_val.insert_str(
                0,
                &vec!["0"; consts::SCALE - scaled_val.len()].join(""),
            );
            scaled_val.insert_str(0, "0.");
        } else {
            scaled_val.insert(scaled_val.len() - consts::SCALE, '.');
        }
        f.write_str(&scaled_val)
    }
}

impl From<u64> for LargeDecimal {
    fn from(val: u64) -> Self {
        Self(Self::identity() * U320::from(val))
    }
}

impl From<u128> for LargeDecimal {
    fn from(val: u128) -> Self {
        Self(Self::identity() * U320::from(val))
    }
}

impl TryAdd<&LargeDecimal> for LargeDecimal {
    fn try_add(&self, rhs: &Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_add(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryAdd<LargeDecimal> for LargeDecimal {
    fn try_add(&self, rhs: Self) -> Result<Self> {
        self.try_add(&rhs)
    }
}

impl TrySub<&LargeDecimal> for LargeDecimal {
    fn try_sub(&self, rhs: &Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_sub(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TrySub<LargeDecimal> for LargeDecimal {
    fn try_sub(&self, rhs: Self) -> Result<Self> {
        self.try_sub(&rhs)
    }
}

impl TryDiv<u64> for LargeDecimal {
    fn try_div(&self, rhs: u64) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_div(U320::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryDiv<u128> for LargeDecimal {
    fn try_div(&self, rhs: u128) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_div(U320::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryDiv<LargeDecimal> for LargeDecimal {
    fn try_div(&self, rhs: Self) -> Result<Self> {
        self.try_div(&rhs)
    }
}

impl TryDiv<&LargeDecimal> for LargeDecimal {
    fn try_div(&self, rhs: &Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(Self::identity())
                .ok_or(DecimalError::MathOverflow)?
                .checked_div(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryMul<u64> for LargeDecimal {
    fn try_mul(&self, rhs: u64) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(U320::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryMul<&LargeDecimal> for LargeDecimal {
    fn try_mul(&self, rhs: &Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(rhs.0)
                .ok_or(DecimalError::MathOverflow)?
                .checked_div(Self::identity())
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryMul<LargeDecimal> for LargeDecimal {
    fn try_mul(&self, rhs: Self) -> Result<Self> {
        self.try_mul(&rhs)
    }
}

impl TryPow<u64> for LargeDecimal {
    /// Calculates base^exp
    fn try_pow(&self, mut exp: u64) -> Result<Self> {
        let mut base = self.clone();
        let mut ret = if exp % 2 != 0 {
            base.clone()
        } else {
            Self::one()
        };

        loop {
            exp /= 2;
            if exp == 0 {
                break;
            }
            base = base.try_mul(&base)?;

            if exp % 2 != 0 {
                ret = ret.try_mul(&base)?;
            }
        }

        Ok(ret)
    }
}

impl TrySqrt for LargeDecimal {
    /// Approximate the square root using Newton's method.
    ///
    /// Based on <https://docs.rs/spl-math/0.1.0/spl_math/precise_number/struct.PreciseNumber.html#method.sqrt>
    fn try_sqrt(&self) -> Result<Self> {
        let two = Self::from(2u64);
        let one = Self::from(1u64);
        // A good initial guess is the average of the interval that contains the
        // input number.  For all numbers, that will be between 1 and the given
        // number.
        let guess = self.try_add(one)?.try_div(two.clone())?;
        newtonian_root_approximation(self.clone(), two, guess)
    }
}

impl TryFrom<LargeDecimal> for Decimal {
    type Error = Error;

    fn try_from(ld: LargeDecimal) -> Result<Self> {
        // we make the [`LargeDecimal`] precision to be same as the [`Decimal`]
        debug_assert!(u192_decimal::consts::WAD > consts::IDENTITY);
        let ld = ld.try_mul(u192_decimal::consts::WAD / consts::IDENTITY)?;
        let LargeDecimal(u320) = ld;
        let U320(words) = u320;
        let [decimal, lowest, mid, overflow1, overflow2] = words;

        if overflow1 != 0 || overflow2 != 0 {
            // the large decimal does not fit the u192
            return Err(error!(DecimalError::MathOverflow));
        }

        Ok(Self(U192([decimal, lowest, mid])))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_scaler() {
        assert_eq!(U320::exp10(consts::SCALE), LargeDecimal::identity());
    }

    #[test]
    fn test_checked_pow() {
        assert_eq!(
            LargeDecimal::one(),
            LargeDecimal::one().try_pow(u64::MAX).unwrap()
        );

        assert_eq!(
            LargeDecimal::two(),
            LargeDecimal::two().try_pow(1u64).unwrap()
        );

        assert_eq!(
            LargeDecimal::from(4u64),
            LargeDecimal::two().try_pow(2u64).unwrap()
        );

        assert_eq!(
            LargeDecimal::from(27_000_000u64),
            LargeDecimal::from(300u64).try_pow(3u64).unwrap()
        );
    }

    #[test]
    fn test_pow_large_numbers() {
        assert_eq!(
            LargeDecimal::from(10u128.pow(3 * 11)),
            LargeDecimal::from(100_000_000_000u64)
                .try_pow(3u64)
                .unwrap()
        );

        assert_eq!(
            LargeDecimal::from(10u128.pow(2 * 11))
                .try_mul(LargeDecimal::from(10u128.pow(2 * 11)))
                .unwrap(),
            LargeDecimal::from(100_000_000_000u64)
                .try_pow(4u64)
                .unwrap()
        );
    }

    #[test]
    fn test_checked_div() {
        assert_eq!(
            LargeDecimal::one().try_div(2u64).unwrap(),
            LargeDecimal::one().try_div(2u128).unwrap(),
        );
    }

    #[test]
    fn test_try_mul() {
        let a = LargeDecimal::from(408000003381369883327u128);
        let b = LargeDecimal::from(1000000007436580456u128);

        assert_eq!(
            "408000006415494734520829188856568457112.000000",
            &a.try_mul(b.clone()).unwrap().to_string()
        );
        assert_eq!("408.000000", &a.try_div(b.clone()).unwrap().to_string());
        assert_eq!("0.002450", &b.try_div(a).unwrap().to_string());
    }

    #[test]
    fn it_sqrts() -> Result<()> {
        assert_eq!(LargeDecimal::zero().try_sqrt()?, LargeDecimal::zero());
        assert_eq!(
            LargeDecimal::from(1u64).try_sqrt()?,
            LargeDecimal::from(1u64)
        );
        assert_eq!(
            LargeDecimal::from(4u64).try_sqrt()?,
            LargeDecimal::from(2u64)
        );
        assert_eq!(
            &Decimal::from(19945u64).try_sqrt()?.to_string(),
            "141.226768000970694167"
        );
        assert_eq!(
            &Decimal::from(19945u64).try_sqrt()?.try_sqrt()?.to_string(),
            "11.883886906268112671"
        );
        assert_eq!(
            &Decimal::from(2u64).try_sqrt()?.to_string(),
            "1.414213562373095048"
        );

        Ok(())
    }

    #[test]
    fn it_converts_large_decimal_to_precise_decimal() -> Result<()> {
        assert_eq!(Decimal::from(4u64), LargeDecimal::from(4u64).try_into()?);
        assert_eq!(
            Decimal::from(1000000u64),
            LargeDecimal::from(1000000u64).try_into()?
        );
        assert_eq!(
            Decimal::one().try_div(Decimal::from(100u64))?,
            LargeDecimal::one()
                .try_div(LargeDecimal::from(100u64))?
                .try_into()?
        );

        Ok(())
    }
}
