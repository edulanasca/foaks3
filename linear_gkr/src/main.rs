use linear_gkr::verifier::ZkVerifier;
use prime_field::FieldElementContext;

use linear_gkr::config::Paths;
use std::{env, process};
fn main() {
  let args: Vec<String> = env::args().collect();
  let paths = Paths::build(env::args()).unwrap_or_else(|err| {
    eprintln!("Problem parsing arguments: {err}");
    process::exit(1)
  });

  //Below unsafe function set packed 64-bit integers, it is mandatory?
  unsafe {
    FieldElementContext::init();
  }
  let mut zk_verifier = ZkVerifier::new();

  let bit_length = zk_verifier.read_circuit(&paths.file_path, &paths.meta_path);

  let result = zk_verifier.verify(&args[4], bit_length.unwrap());
  //let result = zk_verifier.virgo_verify(&args[4], bit_length);
  println!("Pass verification? : {}", result);
}
