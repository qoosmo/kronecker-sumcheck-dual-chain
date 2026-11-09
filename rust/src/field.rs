//! Goldilocks field and its cubic extension `K = Fp[x]/(x^3 - W)`, `W = 2`.
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

/// p = 2^64 - 2^32 + 1.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;
/// Generator of Fp^*.
pub const MULT_GEN: u64 = 7;
/// x^3 - W is irreducible over Fp (checked in tests: W is not a cube).
pub const W: u64 = 2;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct Fp(pub u64);

impl Fp {
    pub const ZERO: Fp = Fp(0);
    pub const ONE: Fp = Fp(1);
    pub fn new(x: u64) -> Fp {
        Fp(x % P)
    }
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }
    pub fn pow(self, mut e: u64) -> Fp {
        let (mut b, mut r) = (self, Fp::ONE);
        while e > 0 {
            if e & 1 == 1 {
                r = r * b;
            }
            b = b * b;
            e >>= 1;
        }
        r
    }
    pub fn inv(self) -> Fp {
        assert!(!self.is_zero(), "inverse of zero in Fp");
        self.pow(P - 2)
    }
}

impl Add for Fp {
    type Output = Fp;
    fn add(self, o: Fp) -> Fp {
        Fp(((self.0 as u128 + o.0 as u128) % P as u128) as u64)
    }
}
impl Sub for Fp {
    type Output = Fp;
    fn sub(self, o: Fp) -> Fp {
        Fp(((self.0 as u128 + P as u128 - o.0 as u128) % P as u128) as u64)
    }
}
impl Mul for Fp {
    type Output = Fp;
    fn mul(self, o: Fp) -> Fp {
        Fp(((self.0 as u128 * o.0 as u128) % P as u128) as u64)
    }
}
impl Neg for Fp {
    type Output = Fp;
    fn neg(self) -> Fp {
        Fp::ZERO - self
    }
}
impl Div for Fp {
    type Output = Fp;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, o: Fp) -> Fp {
        self * o.inv()
    }
}

/// Element a0 + a1 x + a2 x^2 of K.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Hash)]
pub struct K(pub [Fp; 3]);

impl K {
    pub const ZERO: K = K([Fp::ZERO; 3]);
    pub const ONE: K = K([Fp::ONE, Fp::ZERO, Fp::ZERO]);
    pub fn from_fp(x: Fp) -> K {
        K([x, Fp::ZERO, Fp::ZERO])
    }
    pub fn from_u64(x: u64) -> K {
        K::from_fp(Fp::new(x))
    }
    pub fn is_zero(self) -> bool {
        self == K::ZERO
    }
    pub fn pow(self, mut e: u64) -> K {
        let (mut b, mut r) = (self, K::ONE);
        while e > 0 {
            if e & 1 == 1 {
                r = r * b;
            }
            b = b * b;
            e >>= 1;
        }
        r
    }
    /// Inverse by solving M_a b = e_0, where M_a is multiplication by a.
    pub fn inv(self) -> K {
        let w = Fp(W);
        let [a0, a1, a2] = self.0;
        // Columns: a, a*x, a*x^2.
        let mut m = [
            [a0, w * a2, w * a1, Fp::ONE],
            [a1, a0, w * a2, Fp::ZERO],
            [a2, a1, a0, Fp::ZERO],
        ];
        for col in 0..3 {
            let piv = (col..3)
                .find(|&r| !m[r][col].is_zero())
                .expect("inverse of zero in K");
            m.swap(col, piv);
            let iv = m[col][col].inv();
            for j in 0..4 {
                m[col][j] = m[col][j] * iv;
            }
            for r in 0..3 {
                if r != col {
                    let f = m[r][col];
                    if !f.is_zero() {
                        for j in 0..4 {
                            m[r][j] = m[r][j] - f * m[col][j];
                        }
                    }
                }
            }
        }
        K([m[0][3], m[1][3], m[2][3]])
    }
}

impl Add for K {
    type Output = K;
    fn add(self, o: K) -> K {
        K([self.0[0] + o.0[0], self.0[1] + o.0[1], self.0[2] + o.0[2]])
    }
}
impl Sub for K {
    type Output = K;
    fn sub(self, o: K) -> K {
        K([self.0[0] - o.0[0], self.0[1] - o.0[1], self.0[2] - o.0[2]])
    }
}
impl Mul for K {
    type Output = K;
    fn mul(self, o: K) -> K {
        let w = Fp(W);
        let [a0, a1, a2] = self.0;
        let [b0, b1, b2] = o.0;
        K([
            a0 * b0 + w * (a1 * b2 + a2 * b1),
            a0 * b1 + a1 * b0 + w * (a2 * b2),
            a0 * b2 + a1 * b1 + a2 * b0,
        ])
    }
}
impl Neg for K {
    type Output = K;
    fn neg(self) -> K {
        K::ZERO - self
    }
}
impl Div for K {
    type Output = K;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, o: K) -> K {
        self * o.inv()
    }
}
macro_rules! assign_ops {
    ($t:ty) => {
        impl AddAssign for $t {
            fn add_assign(&mut self, o: $t) {
                *self = *self + o;
            }
        }
        impl SubAssign for $t {
            fn sub_assign(&mut self, o: $t) {
                *self = *self - o;
            }
        }
        impl MulAssign for $t {
            fn mul_assign(&mut self, o: $t) {
                *self = *self * o;
            }
        }
    };
}
assign_ops!(Fp);
assign_ops!(K);

/// Primitive n-th root of unity in Fp (n | p - 1).
pub fn root_of_unity(n: u64) -> Fp {
    assert!((P - 1) % n == 0, "n does not divide p - 1");
    Fp(MULT_GEN).pow((P - 1) / n)
}

/// The point omega_n^t of mu_n, as an element of K.
pub fn domain_point(n: usize, t: usize) -> K {
    K::from_fp(root_of_unity(n as u64).pow(t as u64))
}
