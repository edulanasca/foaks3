use prime_field::FieldElement;
#[derive(Debug, Clone)]

pub struct LinearPoly {
  pub a: FieldElement,
  pub b: FieldElement,
}

impl LinearPoly {
  //maps from FieldElement to LinearPoly
  // unfinished, check C/C++ repo
  pub fn maps(arg: FieldElement) -> Self {
    Self { a: arg, b: arg }
  }

  pub fn zero() -> Self {
    Self {
      a: FieldElement::zero(),
      b: FieldElement::zero(),
    }
  }
  pub fn new(a: FieldElement, b: FieldElement) -> Self {
    Self { a, b }
  }
  // Create a monomial with no variables
  pub fn new_constant_monomial(b: FieldElement) -> Self {
    Self {
      a: FieldElement::from_real(0),
      b,
    }
  }

  pub fn eval(&self, x: FieldElement) -> FieldElement {
    self.a * x + self.b
  }
}
impl core::ops::Add for LinearPoly {
  type Output = Self;

  fn add(self, x: Self) -> Self::Output {
    let a = self.a + x.a;
    let b = self.b + x.b;
    Self { a, b }
  }
}

impl core::ops::Mul for LinearPoly {
  type Output = QuadraticPoly;

  fn mul(self, x: Self) -> Self::Output {
    let a = self.a * x.a;
    let b = self.a * x.b + self.b * x.a;
    let c = self.b * x.b;
    QuadraticPoly::new(a, b, c)
  }
}
#[derive(Debug, Clone, Copy)]
pub struct QuadraticPoly {
  pub a: FieldElement,
  pub b: FieldElement,
  pub c: FieldElement,
}

impl QuadraticPoly {
  pub fn zero() -> Self {
    Self {
      a: FieldElement::zero(),
      b: FieldElement::zero(),
      c: FieldElement::zero(),
    }
  }
  pub fn new(a: FieldElement, b: FieldElement, c: FieldElement) -> Self {
    Self { a, b, c }
  }
  //todo: debug function
  pub fn eval(self, x: &FieldElement) -> FieldElement {
    (self.a * *x + self.b) * *x + self.c
  }

  pub fn mul(self, x: LinearPoly) -> CubicPoly {
    let a = self.a * x.a;
    let b = self.a * x.b + self.b * x.a;
    let c = self.b * x.b + self.c * x.a;
    let d = self.c * x.b;
    CubicPoly::new(a, b, c, d)
  }
}

impl core::ops::Add for QuadraticPoly {
  type Output = Self;

  fn add(self, x: Self) -> Self::Output {
    let a = self.a + x.a;
    let b = self.b + x.b;
    let c = self.c + x.c;
    Self { a, b, c }
  }
}

pub struct CubicPoly {
  pub a: FieldElement,
  pub b: FieldElement,
  pub c: FieldElement,
  pub d: FieldElement,
}

impl CubicPoly {
  pub fn new(a: FieldElement, b: FieldElement, c: FieldElement, d: FieldElement) -> Self {
    Self { a, b, c, d }
  }
  pub fn eval(self, x: FieldElement) -> FieldElement {
    ((self.a * x + self.b) * x + self.c) * x + self.d
  }
}

impl core::ops::Add for CubicPoly {
  type Output = Self;

  fn add(self, x: Self) -> Self::Output {
    let a = self.a + x.a;
    let b = self.b + x.b;
    let c = self.c + x.c;
    let d = self.d + x.d;
    Self { a, b, c, d }
  }
}
pub struct QuadruplePoly {
  pub a: FieldElement,
  pub b: FieldElement,
  pub c: FieldElement,
  pub d: FieldElement,
  pub e: FieldElement,
}

impl QuadruplePoly {
  pub fn new(
    a: FieldElement,
    b: FieldElement,
    c: FieldElement,
    d: FieldElement,
    e: FieldElement,
  ) -> Self {
    Self { a, b, c, d, e }
  }
  pub fn eval(self, x: FieldElement) -> FieldElement {
    (((self.a * x + self.b) * x + self.c) * x + self.d) * x + self.e
  }
}

impl core::ops::Add for QuadruplePoly {
  type Output = Self;

  fn add(self, x: Self) -> Self::Output {
    let a = self.a + x.a;
    let b = self.b + x.b;
    let c = self.c + x.c;
    let d = self.d + x.d;
    let e = self.e + x.e;
    Self { a, b, c, d, e }
  }
}

pub struct QuintuplePoly {
  pub a: FieldElement,
  pub b: FieldElement,
  pub c: FieldElement,
  pub d: FieldElement,
  pub e: FieldElement,
  pub f: FieldElement,
}

impl QuintuplePoly {
  pub fn new(
    a: FieldElement,
    b: FieldElement,
    c: FieldElement,
    d: FieldElement,
    e: FieldElement,
    f: FieldElement,
  ) -> Self {
    Self { a, b, c, d, e, f }
  }

  // pub fn operator(x: Self) {
  //     return Self {
  //         a + x.a, b + x.b, c + x.c, d + x.d, e + x.e, f + x.f
  //     }
  // }

  pub fn eval(self, x: FieldElement) -> FieldElement {
    return (((((self.a * x) + self.b) * x + self.c) * x + self.d) * x + self.e) * x + self.f;
  }
}

impl core::ops::Add for QuintuplePoly {
  type Output = Self;

  fn add(self, x: Self) -> Self::Output {
    let a = self.a + x.a;
    let b = self.b + x.b;
    let c = self.c + x.c;
    let d = self.d + x.d;
    let e = self.e + x.e;
    let f = self.f + x.f;
    Self { a, b, c, d, e, f }
  }
}

#[cfg(test)]
mod polynomial {
  use prime_field::FieldElement;

  use crate::polynomial::{CubicPoly, LinearPoly, QuadraticPoly};

  #[test]
  fn exploration() {
    let a = FieldElement::new(1, 0);
    let b = FieldElement::new(1, 0);
    let c = FieldElement::new(2, 0);
    let d = FieldElement::new(2, 0);

    let linear_1 = LinearPoly::new(a, b);
    let linear_2 = QuadraticPoly::new(a, b, c);
    let linear_3 = CubicPoly::new(a, b, c, d);
    let linear_32 = CubicPoly::new(c, d, c, d);

    let linear = QuadraticPoly::new(a, b, d);
    // let sum = linear_3.add(linear_32);
    //let multi = linear_2.mul(linear);
    // println!("{:?}", sum);
    // println!("{:?}", sum);

    assert_eq!(2 + 2, 4);
  }
}
