use infrastructure::merkle_tree::{create_tree, hash_single_field_element};
use std::{char::MAX, thread::current};

use infrastructure::{
  constants::{LOG_SLICE_NUMBER, RS_CODE_RATE, SLICE_NUMBER},
  my_hash::{self, HashDigest},
};

use poly_commitment::LdtCommitment;
use prime_field::FieldElement;

use crate::fri::FRIContext;

pub fn verify_merkle(
  hash_digest: HashDigest,
  merkle_path: Vec<HashDigest>,
  len: usize,
  pow: i32,
  values: Vec<(FieldElement, FieldElement)>,
) -> bool {
  // We need to make sure the len is always smaller than the size of merklePath.
  assert!(merkle_path.len() >= len);

  let mut pow = pow;
  let current_hash: HashDigest = *merkle_path.last().unwrap();

  // don't mutate the current_hash, this is the output of the loop following
  let mut new_hash = HashDigest::new();

  for i in 0..(len - 1) {
    if (pow & i as i32).is_positive() {
      let data: [HashDigest; 2] = [merkle_path[i], current_hash];
      new_hash = my_hash::my_hash(data);
    } else {
      let data: [HashDigest; 2] = [current_hash, merkle_path[i]];
      new_hash = my_hash::my_hash(data);
    }
    pow /= 2;
  }

  let mut value_hash = HashDigest::new();

  unsafe {
    for value in values {
      let mut data_element: [HashDigest; 2] = [
        hash_single_field_element(value.0),
        hash_single_field_element(value.1),
      ];
      data_element[1] = value_hash;
      value_hash = my_hash::my_hash(data_element);
    }
  }

  hash_digest == new_hash && merkle_path.last() == Some(&value_hash)
}

impl FRIContext {
  /// Request two values w^{pow0} and w^{pow1}, with merkle tree proof, where w is the root of unity and w^{pow0} and w^{pow1} are quad residue. Repeat ldt_repeat_num times, storing all result in vector.
  pub fn request_init_value_with_merkle(
    &mut self,
    pow_0: usize,
    pow_1: usize,
    // new_size: &i64,
    oracle_indicator: usize,
  ) -> (Vec<(FieldElement, FieldElement)>, Vec<HashDigest>) {
    // we swap pow_0 and pow_1 when pow_0 > pow_1
    let (pow_0, pow_1) = if pow_0 > pow_1 {
      (pow_1, pow_0)
    } else {
      (pow_0, pow_1)
    };

    assert!(pow_0 + (1 << self.log_current_witness_size_per_slice) / 2 == pow_1);

    let mut value: Vec<(FieldElement, FieldElement)> = vec![];
    let log_leaf_size = LOG_SLICE_NUMBER + 1;

    let mut new_size = 0;
    for i in 0..SLICE_NUMBER {
      let element_1 =
        self.witness_rs_codeword_interleaved[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 0];

      let element_2 =
        self.witness_rs_codeword_interleaved[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 1];

      value.push((element_1, element_2));

      if !self.visited_witness[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 0] {
        self.visited_witness[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 0] = true;
      }
      if !self.visited_witness[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 1] {
        self.visited_witness[oracle_indicator][pow_0 << log_leaf_size | i << 1 | 1] = true;
      }
      new_size += std::mem::size_of::<FieldElement>();
    }

    let depth = self.log_current_witness_size_per_slice - 1;
    let mut com_hhash: Vec<HashDigest> = Vec::with_capacity(depth);

    // minus 1 since each leaf have 2 values (qual resi)
    let mut pos = pow_0 + (1 << (self.log_current_witness_size_per_slice - 1));

    let mut test_hash = self.witness_merkle[oracle_indicator][pos];
    com_hhash[depth] = test_hash;

    for i in 0..depth {
      if !self.visited_init[oracle_indicator][pos ^ 1] {
        new_size += std::mem::size_of::<HashDigest>();
      }
      self.visited_init[oracle_indicator][pos] = true;
      self.visited_init[oracle_indicator][pos ^ 1] = true;

      let data = if (pos & 1) == 1 {
        [self.witness_merkle[oracle_indicator][pos ^ 1], test_hash]
      } else {
        [test_hash, self.witness_merkle[oracle_indicator][pos ^ 1]]
      };
      test_hash = my_hash::my_hash(data);

      com_hhash[i] = self.witness_merkle[oracle_indicator][pos ^ 1];
      pos /= 2;

      assert_eq!(test_hash, self.witness_merkle[oracle_indicator][pos]);
    }
    assert!(pos == 1);
    (value, com_hhash)
  }

  /// Request the merkle proof to lvl-th level oracle, at w^{pow}, will also return it's quad residue's proof.
  /// returned value is unordered, meaning that one of them is the requested value and the other one is it's qual residue.
  pub fn request_step_commit(
    &mut self,
    lvl: usize,
    pow: usize,
    new_size: i64,
  ) -> (Vec<(FieldElement, FieldElement)>, Vec<HashDigest>) {
    let mut new_size = 0;
    let mut pow_0 = 0;

    let mut value_vec: Vec<(FieldElement, FieldElement)> = vec![];
    let mut visited_element = false;

    for i in 0..SLICE_NUMBER {
      pow_0 = self.cpd.rs_codeword_mapping[lvl][pow << LOG_SLICE_NUMBER | i];
      pow_0 /= 2;
      if !self.visited[lvl][pow_0 * 2] {
        self.visited[lvl][pow_0 * 2] = true;
      } else {
        visited_element = true
      }

      value_vec.push((
        self.cpd.rs_codeword[lvl][pow_0 * 2],
        self.cpd.rs_codeword[lvl][pow_0 * 2 + 1],
      ));
    }

    // this can be compressed into one by random linear combination
    if !visited_element {
      new_size += std::mem::size_of::<FieldElement>();
    }

    let mut com_hhash: Vec<HashDigest> = vec![];
    let merkle_size = self.cpd.merkle_size[lvl];
    let val_hhash = self.cpd.merkle[lvl][pow_0];
    pow_0 = (self.cpd.rs_codeword_mapping[lvl][pow << LOG_SLICE_NUMBER] >> (LOG_SLICE_NUMBER + 1))
      + merkle_size;

    while pow_0 != 1 {
      if !self.visited[lvl][pow_0 ^ 1] {
        new_size += std::mem::size_of::<HashDigest>();
        self.visited[lvl][pow_0 ^ 1] = true;
        self.visited[lvl][pow_0] = true;
      }
      com_hhash.push(self.cpd.merkle[lvl][pow_0 ^ 1]);
      pow_0 /= 2;
    }

    com_hhash.push(val_hhash);
    (value_vec, com_hhash)
  }

  /// Given fold parameter r, return the root of the merkle tree of next level.
  pub fn commit_phrase_step(&mut self, r: FieldElement) -> HashDigest {
    let nxt_witness_size = (1 << self.log_current_witness_size_per_slice) / 2;
    if self.cpd.rs_codeword[self.current_step_no].is_empty() {
      self.cpd.rs_codeword[self.current_step_no] =
        vec![FieldElement::default(); nxt_witness_size * (1 << SLICE_NUMBER)];
    }

    let mut previous_witness: Vec<FieldElement> = vec![];
    let mut previous_witness_mapping: Vec<usize> = vec![];

    let (previous_witness, previous_witness_mapping) = match self.current_step_no {
      0 => (
        self.virtual_oracle_witness.clone(),
        self.virtual_oracle_witness_mapping.clone(),
      ),
      _ => (
        self.cpd.rs_codeword[self.current_step_no - 1].clone(),
        self.cpd.rs_codeword_mapping[self.current_step_no - 1].clone(),
      ),
    };

    let inv_2 = FieldElement::default().inverse();

    let log_leaf_size = LOG_SLICE_NUMBER + 1;

    for i in 0..nxt_witness_size {
      let qual_res_0 = i;
      let qual_res_1 = (1 << (self.log_current_witness_size_per_slice - 1) + i) / 2;
      let pos = usize::min(qual_res_0, qual_res_1);

      let inv_mu = self.l_group[((1 << self.log_current_witness_size_per_slice) - i)
        & ((1 << self.log_current_witness_size_per_slice) - 1)];

      for j in 0..SLICE_NUMBER {
        let real_pos = previous_witness_mapping[(pos) << LOG_SLICE_NUMBER | j];
        // assert((i << LOG_SLICE_NUMBER | j) < nxt_witness_size * SLICE_COUNT);
        // we should check this since the original code has BUG comment
        self.cpd.rs_codeword[self.current_step_no][i << LOG_SLICE_NUMBER | j] = inv_2
          * (previous_witness[real_pos] + previous_witness[real_pos | 1])
          + inv_mu * r * (previous_witness[real_pos] - previous_witness[real_pos | 1]);
      }
    }

    for i in 0..nxt_witness_size {
      self.l_group[i] = self.l_group[i * 2];
    }

    // we assume poly_commit::slice_count is (1 << SLICE_NUMBER) here
    let mut tmp: Vec<FieldElement> =
      vec![FieldElement::new_random(); nxt_witness_size * (1 << SLICE_NUMBER)];
    self.cpd.rs_codeword_mapping[self.current_step_no] =
      vec![0; nxt_witness_size * (1 << SLICE_NUMBER)];

    for i in 0..nxt_witness_size / 2 {
      for j in 0..SLICE_NUMBER {
        let a = i << LOG_SLICE_NUMBER | j;
        let b = (i + nxt_witness_size / 2) << LOG_SLICE_NUMBER | j;
        let c = (i) << log_leaf_size | (j << 1) | 0;
        let d = (i) << log_leaf_size | (j << 1) | 1;

        self.cpd.rs_codeword_mapping[self.current_step_no][a] = (i) << log_leaf_size | (j << 1) | 0;
        self.cpd.rs_codeword_mapping[self.current_step_no][b] = (i) << log_leaf_size | (j << 1) | 0;

        tmp[c] = self.cpd.rs_codeword[self.current_step_no][i << LOG_SLICE_NUMBER | j];
        tmp[d] = self.cpd.rs_codeword[self.current_step_no]
          [(i + nxt_witness_size / 2) << LOG_SLICE_NUMBER | j];

        assert!(a < nxt_witness_size * SLICE_NUMBER);
        assert!(b < nxt_witness_size * SLICE_NUMBER);
        assert!(c < nxt_witness_size * SLICE_NUMBER);
        assert!(d < nxt_witness_size * SLICE_NUMBER);
      }
    }

    self.cpd.rs_codeword[self.current_step_no] = tmp;

    self.visited[self.current_step_no] = vec![false; nxt_witness_size * (1 << SLICE_NUMBER) * 4];

    let mut htmp: HashDigest = HashDigest::default();
    let mut hash_val: Vec<HashDigest> = vec![HashDigest::default(); nxt_witness_size / 2];

    unsafe {
      for i in 0..nxt_witness_size / 2 {
        for j in 0..(1 << LOG_SLICE_NUMBER) {
          let mut data = [HashDigest::default(), HashDigest::default()];
          let c = (i) << log_leaf_size | (j << 1) | 0;
          let d = (i) << log_leaf_size | (j << 1) | 1;

          let data_ele = [
            self.cpd.rs_codeword[self.current_step_no][c],
            self.cpd.rs_codeword[self.current_step_no][d],
          ];

          data[0] = hash_single_field_element(data_ele[0]);
          data[1] = htmp;
        }
        hash_val[i] = htmp;
      }

      // write merkle tree to self.cpd.merkle[self.current_step_no]
      let current_step_no = self.cpd.merkle[self.current_step_no].clone();
      create_tree(
        hash_val,
        nxt_witness_size / 2,
        self.cpd.merkle[self.current_step_no].as_mut(),
        Some(std::mem::size_of::<HashDigest>()),
        Some(current_step_no.is_empty()),
      )
    }

    self.cpd.merkle_size[self.current_step_no] = nxt_witness_size / 2;
    self.log_current_witness_size_per_slice -= 1;

    self.current_step_no += 1;
    self.cpd.merkle[self.current_step_no - 1][1] // since we increment current_step_no up there
  }

  /// Return the final rs code since it is only constant size
  pub fn commit_phase_final(&self) -> Vec<FieldElement> {
    self.cpd.rs_codeword[self.current_step_no - 1].clone()
  }

  pub fn commit_phase(&mut self, log_length: usize) -> LdtCommitment {
    // let log_current_witness_size_per_slice_cp = self.log_current_witness_size_per_slice;
    // assumming we already have the initial commit
    let mut codeword_size = 1 << (log_length + RS_CODE_RATE - LOG_SLICE_NUMBER);
    // repeat until the codeword is constant
    let mut ret: Vec<HashDigest> = Vec::with_capacity(log_length + RS_CODE_RATE - LOG_SLICE_NUMBER);
    let mut randomness: Vec<FieldElement> =
      Vec::with_capacity(log_length + RS_CODE_RATE - LOG_SLICE_NUMBER);

    let mut ptr = 0;
    while codeword_size > 1 << RS_CODE_RATE {
      assert!(ptr < log_length + RS_CODE_RATE - LOG_SLICE_NUMBER);
      randomness[ptr] = FieldElement::new_random();
      ret[ptr] = self.commit_phrase_step(randomness[ptr]);
      codeword_size /= 2;
      ptr += 1;
    }

    LdtCommitment {
      commitment_hash: ret,
      final_rs_code: self.commit_phase_final(),
      randomness,
      mx_depth: ptr,
    }
  }
}
