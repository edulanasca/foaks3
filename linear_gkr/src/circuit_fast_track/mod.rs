use std::collections::HashMap;

use prime_field::FieldElement;
#[derive(Debug, Clone, Default)]

pub struct Gate {
  pub ty: usize,
  pub u: usize,
  pub v: usize,
  pub src: Vec<usize>,
  pub weight: Vec<FieldElement>,
  pub parameter_length: usize,
}

/*impl Default for Gate {
    fn default() -> Self {
        Self {
            ty: 2,
            u: 0,
            v: 0,
            src: vec![],
            weight: vec![],
            parameter_length: 0,
        }
    }
}*/
impl Gate {
  pub fn new() -> Self {
    Self {
      ty: 2,
      ..Default::default()
    }
  }

  pub fn from_params(ty: usize, u: usize, v: usize) -> Self {
    Self {
      ty,
      u,
      v,
      ..Default::default()
    }
  }
}

#[derive(Default, Debug, Clone)]
pub struct Layer {
  pub src_expander_c_mempool: Vec<i32>,
  pub src_expander_d_mempool: Vec<i32>,
  pub weight_expander_c_mempool: Vec<FieldElement>,
  pub weight_expander_d_mempool: Vec<FieldElement>,
  pub gates: Vec<Gate>,
  pub bit_length: usize,
  pub u_gates: HashMap<i32, Vec<(i32, (i32, i32))>>,
  pub v_gates: HashMap<i32, Vec<(i32, (i32, i32))>>,
  pub is_parallel: bool,
  pub block_size: usize,
  pub log_block_size: usize,
  pub repeat_num: usize,
  pub log_repeat_num: usize,
}

impl Layer {
  pub fn new() -> Self {
    Default::default()
  }
}

#[derive(Default, Debug, Clone)]
pub struct LayeredCircuit {
  pub circuit: Vec<Layer>,
  pub total_depth: usize,
  pub nputs: Vec<FieldElement>,
}

impl LayeredCircuit {
  pub fn new() -> Self {
    Default::default()
  }
}
