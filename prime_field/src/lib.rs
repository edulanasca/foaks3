#![feature(bigint_helper_methods)]

pub mod error;
pub mod ops;

use std::sync::atomic::AtomicBool;

use ethnum::{i256, AsI256};
use serde::Serialize;

use self::error::{PrimeFieldError, RootOfUnityError};

pub const MOD: u64 = 2305843009213693951;

pub static INITIALIZED: AtomicBool = AtomicBool::new(false);

pub const MASK: u32 = 4294967295; // 2^32 - 1
pub const PRIME: u64 = 2305843009213693951; // 2^61 - 1

pub const MAX_ORDER: usize = 62;

pub fn my_mod(x: u64) -> u64 {
    (x >> 61) + (x & MOD)
}

pub fn my_mult(x: u64, y: u64) -> u64 {
    // return a value between [0, 2PRIME) = x * y mod PRIME
    // return ((hi << 3) | (lo >> 61)) + (lo & PRIME)
    let (lo, hi) = x.widening_mul(y);
    ((hi << 3) | (lo >> 61)) + (lo & PRIME)
}

pub fn packed_my_mult(x: i256, y: i256) -> i256 {
    let x_shift = intrinsics::i256::srl(&x, 32);
    let y_shift = intrinsics::i256::srl(&y, 32);

    let ac = x_shift * y_shift;
    let ad = x_shift * y;
    let bc = x * y_shift;
    let bd = x * y;

    let ad_bc = ad + bc;
    let bd_srl32 = intrinsics::i256::srl(&bd, 32);
    let ad_bc_srl32 = intrinsics::i256::srl(&(ad_bc + bd_srl32), 32);
    let ad_bc_sll32 = intrinsics::i256::sll(&ad_bc, 32);

    let hi = ac + ad_bc_srl32;
    let lo = bc + ad_bc_sll32;

    // ((hi << 3) | (lo >> 61)) + (lo & PRIME)
    (intrinsics::i256::sll(&hi, 3) | intrinsics::i256::srl(&lo, 61)) + (lo & PRIME.as_i256())
}

pub fn packed_my_mod(x: i256) -> i256 {
    // (x >> 61) + (x & mod)
    intrinsics::i256::srl(&x, 61) + (x & MOD.as_i256())
}

#[derive(Serialize, Default, Debug, PartialEq, Eq, Copy, Clone)]
pub struct FieldElement {
    pub real: u64,
    pub img: u64,
}

impl FieldElement {
    fn to_owned_bytes(self) -> Result<Vec<u8>, PrimeFieldError> {
        Ok(bincode::serialize(&self)?)
    }

    pub fn bit_stream(&self) -> Result<Vec<u8>, PrimeFieldError> {
        self.to_owned_bytes()
    }

    pub fn size(&self) -> usize {
        std::mem::size_of::<Self>()
    }

    pub fn new_random() -> Self {
        let real = rand::random::<u64>() % MOD;
        let img = rand::random::<u64>() % MOD;

        Self::new(real, img)
    }

    pub fn new_random_real_only() -> Self {
        let real = rand::random::<u64>() % MOD;

        Self::new(real, 0)
    }

    pub const fn from_real(real: u64) -> Self {
        let real = real % MOD;
        Self { img: 0, real }
    }

    pub const fn from_img(img: u64) -> Self {
        let img = img % MOD;
        Self { img, real: 0 }
    }

    pub const fn new(real: u64, img: u64) -> Self {
        Self { img, real }
    }

    pub const fn zero() -> Self {
        Self::new(0, 0)
    }

    pub const fn real_one() -> Self {
        Self::new(1, 0)
    }

    pub fn sum_parts(&self) -> u64 {
        self.real + self.img
    }

    pub fn inverse(self) -> Self {
        let p: u128 = 2305843009213693951;
        self.fast_pow(p * p - 2)
    }

    pub fn fast_pow(self, mut p: u128) -> FieldElement {
        let mut ret = FieldElement::real_one();
        let mut tmp = self;

        while p != 0 {
            if p & 1 != 0 {
                ret = ret * tmp;
            }
            tmp = tmp * tmp;
            p >>= 1;
        }

        ret
    }

    pub fn get_root_of_unity(log_order: usize) -> Result<FieldElement, RootOfUnityError> {
        if log_order >= MAX_ORDER {
            return Err(RootOfUnityError::LogOrderTooHigh);
        }

        let mut rou = FieldElement::new(2147483648, 1033321771269002680);

        for _ in 0..(MAX_ORDER - log_order) {
            rou = rou * rou;
        }

        Ok(rou)
    }

    pub fn random() -> Self {
        unimplemented!()
    }
}

fn verify_lt_mod_once(mut a: u64) -> u64 {
    if a >= MOD {
        a -= MOD;
    }
    a
}

fn verify_lt_mod_many(mut a: u64) -> u64 {
    while a >= MOD {
        a -= MOD;
    }
    a
}
