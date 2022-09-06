use super::*;

impl TrySub<f64> for f64 {
    fn try_sub(&self, rhs: f64) -> Result<Self> {
        let diff = self - rhs;
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryAdd<f64> for f64 {
    fn try_add(&self, rhs: f64) -> Result<Self> {
        let diff = self + rhs;
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryDiv<f64> for f64 {
    fn try_div(&self, rhs: f64) -> Result<Self> {
        let diff = self / rhs;
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryMul<f64> for f64 {
    fn try_mul(&self, rhs: f64) -> Result<Self> {
        let diff = self * rhs;
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TrySqrt for f64 {
    fn try_sqrt(&self) -> Result<Self> {
        let diff = self.sqrt();
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryPow<f64> for f64 {
    fn try_pow(&self, rhs: f64) -> Result<Self> {
        let diff = self.powf(rhs);
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryPow<i32> for f64 {
    fn try_pow(&self, rhs: i32) -> Result<Self> {
        let diff = self.powi(rhs);
        if diff.is_finite() {
            Ok(diff)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    }
}

impl TryRound<u64> for f64 {
    fn try_floor(&self) -> Result<u64> {
        try_cast_u64(*self, |f| f.floor())
    }

    fn try_ceil(&self) -> Result<u64> {
        try_cast_u64(*self, |f| f.ceil())
    }

    fn try_round(&self) -> Result<u64> {
        try_cast_u64(*self, |f| f.round())
    }
}

impl TryRound<u128> for f64 {
    fn try_floor(&self) -> Result<u128> {
        try_cast_u128(*self, |f| f.floor())
    }

    fn try_ceil(&self) -> Result<u128> {
        try_cast_u128(*self, |f| f.ceil())
    }

    fn try_round(&self) -> Result<u128> {
        try_cast_u128(*self, |f| f.round())
    }
}

fn try_cast_u64(f: f64, transform: impl Fn(f64) -> f64) -> Result<u64> {
    if f.is_sign_positive() && f.is_finite() {
        let f_prime = transform(f);
        if f_prime <= u64::MAX as f64 {
            Ok(f_prime as u64)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    } else {
        Err(DecimalError::MathOverflow.into())
    }
}

fn try_cast_u128(f: f64, transform: impl Fn(f64) -> f64) -> Result<u128> {
    if f.is_sign_positive() && f.is_finite() {
        let f_prime = transform(f);
        if f_prime <= u128::MAX as f64 {
            Ok(f_prime as u128)
        } else {
            Err(DecimalError::MathOverflow.into())
        }
    } else {
        Err(DecimalError::MathOverflow.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works_try_sub_for_f64() {
        let x = 10_000_000_000f64;
        let y = 10_000_000_000_000_000_000f64;

        let z = x.try_sub(y).unwrap();

        assert_eq!(z, x - y);
    }

    #[test]
    fn it_fails_try_sub_for_f64_infinite_values() {
        let x = 10_000_000_000f64;
        let y = f64::INFINITY;

        assert!(x
            .try_sub(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_add_for_f64() {
        let x = 10_000_000_000f64;
        let y = 10_000_000_000_000_000_000f64;

        let z = x.try_add(y).unwrap();

        assert_eq!(z, x + y);
    }

    #[test]
    fn it_fails_try_add_for_f64_infinite_values() {
        let x = 10_000_000_000f64;
        let y = f64::INFINITY;

        assert!(x
            .try_add(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_div_for_f64() {
        let x = 10_000_000_000f64;
        let y = 10_000_000_000_000_000_000f64;

        let z = x.try_div(y).unwrap();

        assert_eq!(z, x / y);

        let w = f64::INFINITY;

        assert_eq!(x.try_div(w).unwrap(), 0.0);
    }

    #[test]
    fn it_fails_try_div_for_f64_on_division_by_zero() {
        let x = 10_000_000_000f64;
        let y = 0f64;

        assert!(x
            .try_div(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_div_for_f64_on_infinity_divided() {
        let x = f64::INFINITY;
        let y = 10f64;

        assert!(x
            .try_div(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_mul_for_f64() {
        let x = 10_000_000_000f64;
        let y = 10_000_000_000_000_000_000f64;

        let z = x.try_mul(y).unwrap();

        assert_eq!(z, x * y);

        let w = 0.0;

        assert_eq!(x.try_mul(w).unwrap(), 0.0);
    }

    #[test]
    fn it_fails_try_mul_for_f64_by_multiplying_by_infinity() {
        let x = 10_000_000_000f64;
        let y = f64::INFINITY;

        assert!(x
            .try_mul(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_sqrt_for_f64() {
        let x = 1_000_000_000_000f64;
        assert_eq!(x.try_sqrt().unwrap(), 1_000_000f64);
    }

    #[test]
    fn it_fails_try_sqrt_negative_numbers() {
        let x = -1f64;
        assert!(x
            .try_sqrt()
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_pow() {
        let x = 1_000_000f64;
        let y = 3f64;

        assert_eq!(x.try_pow(y).unwrap(), 1_000_000_000_000_000_000f64);
    }

    #[test]
    fn fails_try_pow() {
        let x = 1_000_000f64;
        let y = f64::INFINITY;

        assert!(x
            .try_pow(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_pow_i32() {
        let x = 1_000_000f64;
        let y = 3f64;

        assert_eq!(x.try_pow(y).unwrap(), 1_000_000_000_000_000_000f64);
    }

    #[test]
    fn fails_try_pow_i32() {
        let x = 1_000_000f64;
        let y = i32::MAX; // enough to get infinity

        assert!(x
            .try_pow(y)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_cast_u64() {
        let x = 1_000_000.01f64;

        let transform = |f: f64| f.floor();

        let x = try_cast_u64(x, transform).unwrap();
        assert_eq!(x, 1_000_000u64);
    }

    #[test]
    fn it_fails_try_cast_for_negative_values() {
        let x = -1_000_000f64;

        let transform = |f: f64| f.floor();

        assert!(try_cast_u64(x, transform)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_cast_for_too_large_values() {
        let x = f64::MAX as f64;
        let transform = |f: f64| f.floor();

        assert!(try_cast_u64(x, transform)
            .unwrap_err()
            .to_string()
            .contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_floor_u64() {
        let x = 1_000_000.4f64;
        assert_eq!(1_000_000u64, x.try_floor().unwrap());

        let x = 1_000_000.9f64;
        assert_eq!(1_000_000u64, x.try_floor().unwrap());
    }

    #[test]
    fn it_works_try_ceil_u64() {
        let x = 1_000_000.9f64;
        assert_eq!(1_000_001u64, x.try_ceil().unwrap());

        let x = 1_000_000.1f64;
        assert_eq!(1_000_001u64, x.try_ceil().unwrap());
    }

    #[test]
    fn it_works_try_round_u64() {
        let x = 1_000_000.9f64;
        assert_eq!(1_000_001u64, x.try_round().unwrap());

        let x = 1_000_000.1f64;
        assert_eq!(1_000_000u64, x.try_round().unwrap());

        let x = 1_000_000.5f64;
        assert_eq!(1_000_001u64, x.try_round().unwrap());
    }

    #[test]
    fn it_fails_try_floor_on_negative_values_u64() {
        let x = -1_000_000.4f64;
        let res: Result<u64> = x.try_floor();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_ceil_on_negative_values_u64() {
        let x = -1_000_000.4f64;
        let res: Result<u64> = x.try_ceil();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_round_on_negative_values_u64() {
        let x = -1_000_000.4f64;
        let res: Result<u64> = x.try_round();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_floor_on_infinity_u64() {
        let x = f64::INFINITY;
        let res: Result<u64> = x.try_floor();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_ceil_on_infinity_u64() {
        let x = f64::INFINITY;
        let res: Result<u64> = x.try_ceil();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_round_on_infinity_u64() {
        let x = f64::INFINITY;
        let res: Result<u64> = x.try_round();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_works_try_floor_u128() {
        let x = 1_000_000.4f64;
        assert_eq!(1_000_000u128, x.try_floor().unwrap());

        let x = 1_000_000.9f64;
        assert_eq!(1_000_000u128, x.try_floor().unwrap());
    }

    #[test]
    fn it_works_try_ceil_u128() {
        let x = 1_000_000.9f64;
        assert_eq!(1_000_001u128, x.try_ceil().unwrap());

        let x = 1_000_000.1f64;
        assert_eq!(1_000_001u128, x.try_ceil().unwrap());
    }

    #[test]
    fn it_works_try_round_u128() {
        let x = 1_000_000.9f64;
        assert_eq!(1_000_001u128, x.try_round().unwrap());

        let x = 1_000_000.1f64;
        assert_eq!(1_000_000u128, x.try_round().unwrap());

        let x = 1_000_000.5f64;
        assert_eq!(1_000_001u128, x.try_round().unwrap());
    }

    #[test]
    fn it_fails_try_floor_on_negative_values_u128() {
        let x = -1_000_000.4f64;
        let res: Result<u128> = x.try_floor();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_ceil_on_negative_values_u128() {
        let x = -1_000_000.4f64;
        let res: Result<u128> = x.try_ceil();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_round_on_negative_values_u128() {
        let x = -1_000_000.4f64;
        let res: Result<u128> = x.try_round();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_floor_on_infinity_u128() {
        let x = f64::INFINITY;
        let res: Result<u128> = x.try_floor();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_ceil_on_infinity_u128() {
        let x = f64::INFINITY;
        let res: Result<u128> = x.try_ceil();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }

    #[test]
    fn it_fails_try_round_on_infinity_u128() {
        let x = f64::INFINITY;
        let res: Result<u128> = x.try_round();
        assert!(res.unwrap_err().to_string().contains("MathOverflow"));
    }
}
