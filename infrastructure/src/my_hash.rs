use byteorder::{BigEndian, ReadBytesExt};
use sha3::{Digest, Sha3_256};
use std::io::Cursor;

/// TODO: https://doc.rust-lang.org/beta/core/arch/x86_64/struct.__m128i.html
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct HashDigest {
  pub h0: i128,
  pub h1: i128,
}

impl HashDigest {
  pub fn new() -> Self {
    HashDigest { h0: 0, h1: 0 }
  }
}

#[inline]
pub fn my_hash(src: [HashDigest; 2]) -> HashDigest {
  // the original sha256_update_shani type signature is an optimised function for
  // SHA-NI instruction sets machine, this is the fallback one
  // https://www.ic.unicamp.br/~ra142685/sok-apkc.pdf
  let mut hasher = Sha3_256::new();

  for d in src {
    // NOTE: Big endian serialisation
    let sixteen_u8_h = d.h0.to_be_bytes();
    let sixteen_u8_l = d.h1.to_be_bytes();
    hasher.update(sixteen_u8_h);
    hasher.update(sixteen_u8_l);
  }

  let result = hasher.finalize();

  // DO WE REALLY SURE SHA256 produces fixed-length output?
  let (arr, _) = result.as_chunks::<{ 16 as usize }>();

  HashDigest {
    // NOTE: Big endian serialisation
    h0: Cursor::new(arr[0]).read_i128::<BigEndian>().unwrap(),
    h1: Cursor::new(arr[1]).read_i128::<BigEndian>().unwrap(),
  }
}
