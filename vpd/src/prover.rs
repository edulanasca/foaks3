use infrastructure::my_hash::HashDigest;
use poly_commitment::PolyCommitContext;

use crate::fri::{request_init_commit, FRIContext};

/// This will returns the merkle root
pub fn vpd_prover_init(log_input_length: usize) -> HashDigest {
  request_init_commit(
    &mut FRIContext::default(),
    PolyCommitContext::default(),
    log_input_length,
    0,
  )
}
