//! Math for preserving precision of token amounts which are limited
//! by the SPL Token program to be at most u64::MAX.
//!
//! Decimals are internally scaled by a WAD (10^18) to preserve
//! precision up to 18 decimal places. Decimals are sized to support
//! both serialization and precise math for the full range of
//! unsigned 64-bit integers. The underlying representation is a
//! u192 rather than u320 to reduce compute cost while losing
//! support for arithmetic operations at the high end of u64 range.

use super::*;
use std::convert::TryFrom;

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
}

impl ScaledVal for Decimal {
    /// Return raw scaled value if it fits within u128
    #[allow(clippy::wrong_self_convention)]
    fn to_scaled_val(&self) -> Result<u128> {
        Ok(u128::try_from(self.0).map_err(|_| DecimalError::MathOverflow)?)
    }

    fn from_scaled_val(scaled_val: u128) -> Self {
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

impl TrySub<&Decimal> for Decimal {
    fn try_sub(&self, rhs: &Self) -> Result<Self> {
        Ok(Self(
            self.0
                .checked_sub(rhs.0)
                .ok_or(DecimalError::MathOverflow)?,
        ))
    }
}

impl TrySub<Decimal> for Decimal {
    fn try_sub(&self, rhs: Self) -> Result<Self> {
        self.try_sub(&rhs)
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
        // Both the numerator `self.0` and the denominator `rhs.0` are scaled up
        // to 1E+18. Since we divide the numerator by the denominator we will
        // have to rescale the value. Depending on when we rescale the
        // calculation we run into lower risk of overflowing.
        match self.0.checked_mul(Self::wad()) {
            // We first try scale the numerator a second time to offset the
            // downscalling that occurs with the `checked_div`
            Some(v) => Ok(Self(
                v.checked_div(rhs.0).ok_or(DecimalError::MathOverflow)?,
            )),
            // If the numerator self.0 is bigger than 1E+39 = 1E+21 * 1E+18,
            // then it will overflow when multiplied by 1E+18 and therefore
            // `check_mul` will return None
            None => {
                let u192 = if self.0 >= rhs.0 {
                    // We divide numerator by denominator and
                    // scale up the result
                    self.0
                        .checked_div(rhs.0)
                        .and_then(|v| v.checked_mul(Self::wad()))
                } else {
                    // We downscale the denominator and then divide the
                    // scaled numerator by the unscaled denominator given
                    // the result is then the scaled result as desired
                    self.0.checked_div(
                        rhs.0
                            .checked_div(Self::wad())
                            .ok_or(DecimalError::MathOverflow)?,
                    )
                };

                if let Some(u192) = u192 {
                    Ok(Self(u192))
                } else {
                    Err(yield_error())
                }
            }
        }
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
        match self.0.checked_mul(rhs.0) {
            Some(v) => Ok(Self(
                v.checked_div(Self::wad())
                    .ok_or(DecimalError::MathOverflow)?,
            )),
            None => {
                let u192 = if self.0 >= rhs.0 {
                    self.0
                        .checked_div(Self::wad())
                        .and_then(|v| v.checked_mul(rhs.0))
                } else {
                    rhs.0
                        .checked_div(Self::wad())
                        .and_then(|v| v.checked_mul(self.0))
                };

                if let Some(u192) = u192 {
                    Ok(Self(u192))
                } else {
                    Err(yield_error())
                }
            }
        }
    }
}

impl AlmostEq for Decimal {}

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
        newtonian_root_approximation(*self, two, guess)
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
    fn test_checked_div_accross_parameter_space() -> Result<()> {
        let num_list: Vec<u128> = vec![
            1,                                                   // 10^1
            10,                                                  // 10^2
            100,                                                 // 10^2
            1_000,                                               // 10^3
            10_000,                                              // 10^4
            100_000,                                             // 10^5
            1_000_000,                                           // 10^6
            10_000_000,                                          // 10^7
            100_000_000,                                         // 10^8
            1_000_000_000,                                       // 10^9
            10_000_000_000,                                      // 10^11
            100_000_000_000,                                     // 10^12
            1_000_000_000_000,                                   // 10^13
            10_000_000_000_000,                                  // 10^14
            100_000_000_000_000,                                 // 10^15
            1_000_000_000_000_000,                               // 10^16
            10_000_000_000_000_000,                              // 10^17
            100_000_000_000_000_000,                             // 10^18
            1_000_000_000_000_000_000,                           // 10^19
            10_000_000_000_000_000_000,                          // 10^20
            100_000_000_000_000_000_000,                         // 10^21
            1_000_000_000_000_000_000_000,                       // 10^22
            10_000_000_000_000_000_000_000,                      // 10^23
            100_000_000_000_000_000_000_000,                     // 10^24
            1_000_000_000_000_000_000_000_000,                   // 10^25
            10_000_000_000_000_000_000_000_000,                  // 10^26
            100_000_000_000_000_000_000_000_000,                 // 10^27
            1_000_000_000_000_000_000_000_000_000,               // 10^28
            10_000_000_000_000_000_000_000_000_000,              // 10^29
            100_000_000_000_000_000_000_000_000_000,             // 10^30
            1_000_000_000_000_000_000_000_000_000_000,           // 10^31
            10_000_000_000_000_000_000_000_000_000_000,          // 10^32
            100_000_000_000_000_000_000_000_000_000_000,         // 10^33
            1_000_000_000_000_000_000_000_000_000_000_000,       // 10^34
            10_000_000_000_000_000_000_000_000_000_000_000,      // 10^35
            100_000_000_000_000_000_000_000_000_000_000_000,     // 10^36
            1_000_000_000_000_000_000_000_000_000_000_000_000,   // 10^37
            10_000_000_000_000_000_000_000_000_000_000_000_000,  // 10^38
            100_000_000_000_000_000_000_000_000_000_000_000_000, // 10^39
        ];

        let mut i = 0;
        for a in num_list.clone() {
            let a_dec = Decimal::from(a);

            let mut j = 0;
            for b in num_list.clone() {
                let b_dec = Decimal::from(b);
                let a_b = a_dec.try_div(b_dec)?;

                let exponent: i32 = i - j;
                let scaled_exponent = exponent + 18;

                let expected = if scaled_exponent < 0 {
                    // This is case where magnitude discrepancy between
                    // numerator and denominator is such that result
                    // aproximates to zero
                    Decimal::zero()
                } else if scaled_exponent <= 38 {
                    // We use scaled exponent to calculate decimal from
                    // scaled value to avoid having to using floating point
                    // numbers
                    Decimal::from_scaled_val(u128::pow(
                        10,
                        scaled_exponent as u32,
                    ))
                } else {
                    // When the scaled exponent is above 38 we are better off
                    // calculating the decimal from a u128 to avoid overflowing
                    Decimal::from(u128::pow(10, exponent as u32))
                };

                assert_eq!(a_b, expected);

                j += 1;
            }
            i += 1;
        }

        Ok(())
    }
    #[test]
    fn test_checked_div() {
        assert_eq!(
            Decimal::one().try_div(2u64).unwrap(),
            Decimal::one().try_div(2u128).unwrap(),
        );

        assert_eq!(
            Decimal::from(5u64).try_div(2u64).unwrap(),
            Decimal::from_scaled_val(2500000000000000000)
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

    #[test]
    fn it_multiplies_large_numbers() {
        let a = Decimal::from(10_000_000_000_000_000_000_u64);
        let b = Decimal::from(10_000_000_000_000_000_000_u64);

        assert_eq!(
            Decimal::from(
                100_000_000_000_000_000_000_000_000_000_000_000_000_u128
            ),
            a.try_mul(b).unwrap()
        );
    }

    #[test]
    fn it_divides_large_numbers() {
        let a = Decimal::from(18_446_744_073_709_551_615_u64);
        let b = Decimal::from(18_446_744_073_709_551_615_u64);
        let c = Decimal::from(1_u64);
        let d = Decimal::from(2_u64);

        assert_eq!(
            Decimal::from(
                340_282_366_920_938_463_426_481_119_284_349_108_225_u128
            ),
            a.try_mul(b).expect("to mul").try_div(c).expect("to div")
        );
        assert_eq!(
            Decimal::from(170141183460469231713240559642174554112u128),
            a.try_mul(b).expect("to mul").try_div(d).expect("to div")
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
