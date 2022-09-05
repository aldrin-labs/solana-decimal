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
        try_cast(*self, |f| f.floor())
    }

    fn try_ceil(&self) -> Result<u64> {
        try_cast(*self, |f| f.ceil())
    }

    fn try_round(&self) -> Result<u64> {
        try_cast(*self, |f| f.round())
    }
}

fn try_cast(f: f64, transform: impl Fn(f64) -> f64) -> Result<u64> {
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
