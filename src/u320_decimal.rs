//! Math for preserving precision of token amounts which are limited
//! by the SPL Token program to be at most u64::MAX.
//!
//! Decimals are internally scaled by an identity (10^6) to preserve
//! precision up to 6 decimal places. Decimals are sized to support
//! both serialization and precise math for the full range of
//! unsigned 64-bit integers. The underlying representation is a u320. This
//! enables arithmetic ops at the high range of u64.

use super::*;

pub mod consts {
    /// Scale of precision.
    pub const SCALE: usize = 9;

    /// Identity
    pub const IDENTITY: u64 = 1_000_000_000;

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
}

impl ScaledVal for LargeDecimal {
    /// Return raw scaled value if it fits within u128
    #[allow(clippy::wrong_self_convention)]
    fn to_scaled_val(&self) -> Result<u128> {
        Ok(u128::try_from(self.0).map_err(|_| DecimalError::MathOverflow)?)
    }

    fn from_scaled_val(scaled_val: u128) -> Self {
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
        match self.0.checked_mul(Self::identity()) {
            Some(v) => Ok(Self(
                v.checked_div(rhs.0).ok_or(DecimalError::MathOverflow)?,
            )),
            None => {
                let u192 = if self.0 >= rhs.0 {
                    self.0
                        .checked_div(rhs.0)
                        .and_then(|v| v.checked_mul(Self::identity()))
                } else {
                    rhs.0
                        .checked_div(self.0)
                        .and_then(|v| v.checked_mul(Self::identity()))
                };

                if let Some(u192) = u192 {
                    Ok(Self(u192))
                } else {
                    Err(error!(DecimalError::MathOverflow))
                }
            }
        }
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
        match self.0.checked_mul(rhs.0) {
            Some(v) => Ok(Self(
                v.checked_div(Self::identity())
                    .ok_or(DecimalError::MathOverflow)?,
            )),
            None => {
                let inner = if self.0 >= rhs.0 {
                    self.0
                        .checked_div(Self::identity())
                        .and_then(|v| v.checked_mul(rhs.0))
                } else {
                    rhs.0
                        .checked_div(Self::identity())
                        .and_then(|v| v.checked_mul(self.0))
                };

                if let Some(inner) = inner {
                    Ok(Self(inner))
                } else {
                    Err(error!(DecimalError::MathOverflow))
                }
            }
        }
    }
}

impl TryMul<LargeDecimal> for LargeDecimal {
    fn try_mul(&self, rhs: Self) -> Result<Self> {
        self.try_mul(&rhs)
    }
}

impl AlmostEq for LargeDecimal {}

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

impl TryFrom<Decimal> for LargeDecimal {
    type Error = Error;

    /// # Important
    /// This conversion loses precision because [`Self`] has less decimal
    /// places than [`Decimal`]
    fn try_from(d: Decimal) -> Result<Self> {
        debug_assert!(u192_decimal::consts::WAD > consts::IDENTITY);
        let d = d.try_div(u192_decimal::consts::WAD / consts::IDENTITY)?;
        let Decimal(u192) = d;
        let U192(words) = u192;
        let [a, b, c] = words;

        Ok(Self(U320([a, b, c, 0, 0])))
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
            "408000006415494734520829188856568457112.000000000",
            &a.try_mul(b.clone()).unwrap().to_string()
        );
        assert_eq!("408.000000347", &a.try_div(b.clone()).unwrap().to_string());
        assert_eq!("0.002450980", &b.try_div(a).unwrap().to_string());
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
    fn it_converts_precise_decimal_to_large_decimal() -> Result<()> {
        assert_eq!(LargeDecimal::from(4u64), Decimal::from(4u64).try_into()?);
        assert_eq!(
            LargeDecimal::from(1000000u64),
            Decimal::from(1000000u64).try_into()?,
        );
        assert_eq!(
            LargeDecimal::one().try_div(LargeDecimal::from(100u64))?,
            Decimal::one().try_div(Decimal::from(100u64))?.try_into()?,
        );
        assert_eq!(
            // 1.123456
            LargeDecimal::from_scaled_val(1_123456111),
            // 1.123456111111111111
            Decimal::from_scaled_val(1_123456_111111111111).try_into()?,
        );

        Ok(())
    }
}
