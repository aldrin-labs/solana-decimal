//! Math for preserving precision of token amounts which are limited
//! by the SPL Token program to be at most u64::MAX.
//!
//! Decimals are internally scaled by a WAD (10^18) to preserve
//! precision up to 18 decimal places. Decimals are sized to support
//! both serialization and precise math for the full range of
//! unsigned 64-bit integers. The underlying representation is a
//! u192 rather than u320 to reduce compute cost while losing
//! support for arithmetic operations at the high end of u64 range.

#![allow(clippy::assign_op_pattern)]
#![allow(clippy::ptr_offset_with_cast)]
#![allow(clippy::manual_range_contains)]

use super::*;

pub mod consts {
    /// Scale of precision.
    pub const SCALE: usize = 18;

    /// Identity
    pub const WAD: u64 = 1_000_000_000_000_000_000;

    pub const TWO_WADS: u64 = WAD * 2;

    pub const HALF_WAD: u64 = WAD / 2;

    pub const PERCENT_SCALER: u64 = 10_000_000_000_000_000;

    pub const PERMILLION_SCALER: u64 = 1_000_000_000_000;
}

/// Large decimal values, precise to 18 digits
#[derive(Clone, Copy, Debug, Default, PartialEq, PartialOrd, Eq, Ord)]
pub struct Decimal(pub U192);

impl Decimal {
    pub fn one() -> Self {
        Self(Self::wad())
    }

    pub fn two() -> Self {
        Self(U192::from(consts::TWO_WADS))
    }

    pub fn zero() -> Self {
        Self(U192::zero())
    }

    // OPTIMIZE: use const slice when fixed in BPF toolchain
    fn wad() -> U192 {
        U192::from(consts::WAD)
    }

    // OPTIMIZE: use const slice when fixed in BPF toolchain
    fn half_wad() -> U192 {
        U192::from(consts::HALF_WAD)
    }

    /// Create scaled decimal from a percent value
    pub fn from_percent(percent: impl Into<u64>) -> Self {
        Self(U192::from(percent.into() * consts::PERCENT_SCALER))
    }

    /// Create scaled decimal from a permillion value
    ///
    /// * 10_000 pm = 1%
    /// * 1_000_000 pm = 100%
    pub fn from_permillion(permillion: impl Into<u64>) -> Self {
        Self(U192::from(permillion.into() * consts::PERMILLION_SCALER))
    }

    /// Return raw scaled value if it fits within u128
    #[allow(clippy::wrong_self_convention)]
    pub fn to_scaled_val(&self) -> Result<u128> {
        Ok(u128::try_from(self.0).map_err(|_| DecimalError::MathOverflow)?)
    }

    pub fn from_scaled_val(scaled_val: u128) -> Self {
        Self(U192::from(scaled_val))
    }
}

impl TryRound<u64> for Decimal {
    fn try_round(&self) -> Result<u64> {
        let rounded_val = Self::half_wad()
            .checked_add(self.0)
            .ok_or(DecimalError::MathOverflow)?
            .checked_div(Self::wad())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(rounded_val)
            .map_err(|_| DecimalError::MathOverflow)?)
    }

    fn try_ceil(&self) -> Result<u64> {
        let ceil_val = Self::wad()
            .checked_sub(U192::from(1u64))
            .ok_or(DecimalError::MathOverflow)?
            .checked_add(self.0)
            .ok_or(DecimalError::MathOverflow)?
            .checked_div(Self::wad())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(ceil_val).map_err(|_| DecimalError::MathOverflow)?)
    }

    fn try_floor(&self) -> Result<u64> {
        let ceil_val = self
            .0
            .checked_div(Self::wad())
            .ok_or(DecimalError::MathOverflow)?;
        Ok(u64::try_from(ceil_val).map_err(|_| DecimalError::MathOverflow)?)
    }
}

impl AlmostEq for Decimal {
    /// The precision is 15 decimal places
    fn almost_eq(&self, other: &Self) -> bool {
        let precision = Self::from_scaled_val(1000);
        match self.cmp(&other) {
            std::cmp::Ordering::Equal => true,
            std::cmp::Ordering::Less => {
                other.try_sub(*self).unwrap() < precision
            }
            std::cmp::Ordering::Greater => {
                self.try_sub(*other).unwrap() < precision
            }
        }
    }
}

impl fmt::Display for Decimal {
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

impl From<u64> for Decimal {
    fn from(val: u64) -> Self {
        Self(Self::wad() * U192::from(val))
    }
}

impl From<u128> for Decimal {
    fn from(val: u128) -> Self {
        Self(Self::wad() * U192::from(val))
    }
}

impl TryAdd<Decimal> for Decimal {
    fn try_add(&self, rhs: Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_add(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TrySub<Decimal> for Decimal {
    fn try_sub(&self, rhs: Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_sub(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryDiv<u64> for Decimal {
    fn try_div(&self, rhs: u64) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_div(U192::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryDiv<u128> for Decimal {
    fn try_div(&self, rhs: u128) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_div(U192::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryDiv<Decimal> for Decimal {
    fn try_div(&self, rhs: Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(Self::wad())
                .ok_or(DecimalError::MathOverflow)?
                .checked_div(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryMul<u64> for Decimal {
    fn try_mul(&self, rhs: u64) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(U192::from(rhs))
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryMul<Decimal> for Decimal {
    fn try_mul(&self, rhs: Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_mul(rhs.0)
                .ok_or(DecimalError::MathOverflow)?
                .checked_div(Self::wad())
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TryPow<u64> for Decimal {
    /// Calculates base^exp
    fn try_pow(&self, mut exp: u64) -> Result<Self> {
        let mut base = self.clone();
        let mut ret = if exp % 2 != 0 { base } else { Self::one() };

        while exp > 0 {
            exp /= 2;
            base = base.try_mul(base.clone())?;

            if exp % 2 != 0 {
                ret = ret.try_mul(base)?;
            }
        }

        Ok(ret)
    }
}

impl TrySqrt for Decimal {
    /// Approximate the square root using Newton's method.
    ///
    /// Based on <https://docs.rs/spl-math/0.1.0/spl_math/precise_number/struct.PreciseNumber.html#method.sqrt>
    fn try_sqrt(&self) -> Result<Self> {
        let two = Self::from(2u64);
        let one = Self::from(1u64);
        // A good initial guess is the average of the interval that contains the
        // input number.  For all numbers, that will be between 1 and the given
        // number.
        let guess = self.try_add(one)?.try_div(two)?;
        newtonian_root_approximation(self.clone(), two, guess)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_scaler() {
        assert_eq!(U192::exp10(consts::SCALE), Decimal::wad());
    }

    #[test]
    fn test_checked_pow() {
        assert_eq!(Decimal::one(), Decimal::one().try_pow(u64::MAX).unwrap());
    }

    #[test]
    fn test_checked_div() {
        assert_eq!(
            Decimal::one().try_div(2u64).unwrap(),
            Decimal::one().try_div(2u128).unwrap(),
        );
    }

    #[test]
    fn test_can_hold_one_wad() {
        assert_eq!(
            Decimal::from(Decimal::one().to_scaled_val().unwrap()),
            Decimal::from(1_000_000_000_000_000_000u128)
        );
    }

    #[test]
    fn test_from_percent() {
        assert_eq!(
            Decimal::from_percent(200u64),
            Decimal::one().try_mul(2).unwrap()
        );
        assert_eq!(Decimal::from_percent(90u64).try_floor().unwrap(), 0);
    }

    #[test]
    fn test_try_mul() {
        let a = Decimal(408000003381369883327u128.into());
        let b = Decimal(1000000007436580456u128.into());

        assert_eq!(
            Decimal(408000006415494734520u128.into()),
            a.try_mul(b).unwrap()
        );
    }

    mod custom_u128 {
        use uint::construct_uint;
        construct_uint! {
            pub struct U128(2);
        }
    }

    // Solana team's implementation had two number types: U192 and U128. We
    // removed the latter. This test makes sure that they two were
    // interchangeable in usage of `from_scaled_val`.
    #[test]
    fn test_decimal_same_as_rate() {
        use custom_u128::U128;

        fn ceil_u192(v: u128) -> u64 {
            let one = U192::from(consts::WAD);
            let v = U192::from(v).checked_div(one).unwrap();
            u64::try_from(v).unwrap()
        }

        fn ceil_u128(v: u64) -> u64 {
            let one = U128::from(consts::WAD);
            let v = U128::from(v).checked_div(one).unwrap();
            u64::try_from(v).unwrap()
        }

        assert_eq!(ceil_u128(0), ceil_u192(0));
        assert_eq!(ceil_u128(1), ceil_u192(1));
        assert_eq!(ceil_u128(10), ceil_u192(10));
        assert_eq!(ceil_u128(1_000), ceil_u192(1_000));
    }

    #[test]
    fn it_represents_percents() {
        let dec = Decimal::one()
            .try_div(Decimal::from(10u64))
            .unwrap()
            .try_mul(Decimal::from(9u64))
            .unwrap();
        assert_eq!(dec.to_string(), "0.900000000000000000");
        assert_eq!(Decimal::from_percent(90u64), dec);
    }

    #[test]
    fn it_represents_permillion() {
        assert_eq!(
            Decimal::from_percent(1u64),
            Decimal::from_permillion(10_000u64)
        );
        assert_eq!(
            Decimal::from_percent(100u64),
            Decimal::from_permillion(1_000_000u64)
        );
        assert_eq!(
            Decimal::from_percent(90u64),
            Decimal::from_permillion(900_000u64)
        );
    }

    #[test]
    fn it_sqrts() -> Result<()> {
        assert_eq!(Decimal::zero().try_sqrt()?, Decimal::zero());
        assert_eq!(Decimal::from(1u64).try_sqrt()?, Decimal::from(1u64));
        assert_eq!(Decimal::from(4u64).try_sqrt()?, Decimal::from(2u64));
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
}
