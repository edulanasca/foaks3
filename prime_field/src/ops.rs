use super::{my_mod, my_mult, verify_lt_mod_many, verify_lt_mod_once, FieldElement, MOD};

impl core::ops::Add for FieldElement {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let real = verify_lt_mod_once(self.real + rhs.real);
        let img = verify_lt_mod_once(self.img + rhs.img);

        Self { real, img }
    }
}

impl core::ops::Sub for FieldElement {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let temp_real = rhs.real ^ MOD;
        let temp_img = rhs.img ^ MOD;

        let real = verify_lt_mod_once(self.real + temp_real);
        let img = verify_lt_mod_once(self.img + temp_img);

        Self { real, img }
    }
}

impl core::ops::Mul for FieldElement {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let all_prod = my_mult(self.sum_parts(), rhs.sum_parts()); // at most 6 * mod

        let ac = my_mult(self.real, rhs.real);
        let mut bd = my_mult(self.img, rhs.img); // at most 1.x * mod
        let mut nac = ac;

        bd = verify_lt_mod_once(bd);
        nac = verify_lt_mod_once(nac);

        nac ^= MOD;
        bd ^= MOD;

        let mut t_img = all_prod + nac + bd; // at most 8 * mod
        t_img = my_mod(t_img);
        t_img = verify_lt_mod_once(t_img);

        let t_real = verify_lt_mod_many(ac + bd);

        Self {
            real: t_real,
            img: t_img,
        }
    }
}

impl core::ops::Neg for FieldElement {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let real = (MOD - self.real) % MOD;
        let img = (MOD - self.img) % MOD;

        Self { real, img }
    }
}
