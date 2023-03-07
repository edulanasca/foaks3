use std::time;

use prime_field::FieldElement;

use infrastructure::constants::*;
use infrastructure::my_hash::HashDigest;
use infrastructure::rs_polynomial::{self, fast_fourier_transform, inverse_fast_fourier_transform};
use infrastructure::utility;

#[derive(Default)]
pub struct LdtCommitment {
  pub commitment_hash: Vec<HashDigest>,
  pub randomness: Vec<FieldElement>,
  pub final_rs_code: Vec<FieldElement>,
  pub mx_depth: usize,
  // repeat_no: usize,
}

#[derive(Default, Debug, Clone)]
pub struct PolyCommitContext {
  pub twiddle_factor: Vec<FieldElement>,
  pub inv_twiddle_factor: Vec<FieldElement>,
  pub twiddle_factor_size: usize,
  pub inner_prod_evals: Vec<FieldElement>,

  pub l_coef: Vec<FieldElement>,
  pub l_coef_len: usize,

  pub l_eval: Vec<FieldElement>,
  pub l_eval_len: usize,
  pub q_coef: Vec<FieldElement>,
  pub q_coef_len: usize,

  pub q_eval: Vec<FieldElement>,
  pub q_eval_len: usize,

  pub lq_coef: Vec<FieldElement>,
  pub lq_eval: Vec<FieldElement>,
  pub h_coef: Vec<FieldElement>,
  pub h_eval: Vec<FieldElement>,

  pub h_eval_arr: Vec<FieldElement>,

  pub slice_size: usize,
  pub slice_count: usize,
  pub slice_real_ele_cnt: usize,
  pub pre_prepare_executed: bool,
}
#[derive(Default, Debug, Clone)]
pub struct PolyCommitProver {
  pub total_time_pc_p: f64,
  ctx: PolyCommitContext,
}

impl PolyCommitProver {
  pub fn commit_private_array(
    &mut self,
    private_array: &[FieldElement],
    log_array_length: usize,
  ) -> HashDigest {
    self.total_time_pc_p = 0.;

    self.ctx.pre_prepare_executed = true;

    let slice_count = 1 << LOG_SLICE_NUMBER;
    self.ctx.slice_count = slice_count;

    let slice_size = 1 << (log_array_length + RS_CODE_RATE - LOG_SLICE_NUMBER);
    self.ctx.slice_size = slice_size;

    let slice_real_ele_cnt = slice_size >> RS_CODE_RATE;
    self.ctx.slice_real_ele_cnt = slice_real_ele_cnt;

    let l_eval_len = slice_count * slice_size;
    self.ctx.l_eval_len = l_eval_len;

    let l_eval = &mut self.ctx.l_eval;
    l_eval.reserve(l_eval_len);

    let mut tmp = Vec::<FieldElement>::with_capacity(slice_real_ele_cnt);

    let order = slice_size * slice_count;

    let now = time::Instant::now();

    let mut scratch_pad = rs_polynomial::ScratchPad::from_order(order);

    for i in 0..slice_count {
      let mut all_zero = true;
      let zero = FieldElement::zero();

      for j in 0..slice_real_ele_cnt {
        if private_array[i * slice_real_ele_cnt + j] == zero {
          continue;
        }
        all_zero = false;
        break;
      }

      if all_zero {
        for j in 0..slice_size {
          l_eval[i * slice_size + j] = zero;
        }
      } else {
        inverse_fast_fourier_transform(
          &mut scratch_pad,
          &private_array[i * slice_real_ele_cnt..],
          slice_real_ele_cnt,
          slice_real_ele_cnt,
          FieldElement::get_root_of_unity(utility::my_log(slice_real_ele_cnt).unwrap()).unwrap(),
          &mut tmp[..],
        );

        fast_fourier_transform(
          &mut scratch_pad.dst,
          &mut scratch_pad.twiddle_factor,
          &mut scratch_pad.twiddle_factor_size,
          &tmp[..],
          slice_real_ele_cnt,
          slice_size,
          FieldElement::get_root_of_unity(utility::my_log(slice_size).unwrap()).unwrap(),
          &mut l_eval[i * slice_size..],
        )
      }
    }

    let elapsed_time = now.elapsed();
    println!("FFT Prepare time: {} ms", elapsed_time.as_millis());

    unimplemented!()
  }
}

#[derive(Default, Debug)]
pub struct PolyCommitVerifier {
  pub pc_prover: PolyCommitProver,
}

pub fn commit_phrase_step(r: FieldElement) -> HashDigest {
  HashDigest::new()
}
