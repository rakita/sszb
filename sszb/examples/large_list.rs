//! Encode and decode a list many times.
//!
//! Useful for `cargo flamegraph`.

use sszb::{Decode, Encode};

fn main() {
    let vec: Vec<u64> = vec![4242; 8196];

    let output: Vec<Vec<u64>> = (0..40_000)
        .map(|_| Vec::from_sszb_bytes(&vec.as_sszb_bytes()).unwrap())
        .collect();

    println!("{}", output.len());
}
