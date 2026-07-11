//! base64 throughput via the `base64` crate (v0.22), the de-facto Rust standard.
//!
//! Mirrors LeanBase64.lean: same sizes, best-of-5 trials, one warmup. Emits CSV
//! `rust,<size>,<encode MiB/s>,<decode MiB/s>` on stdout.
use base64::{engine::general_purpose::STANDARD, Engine};
use std::hint::black_box;
use std::time::Instant;

const SIZES: [usize; 9] = [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576];
const WORK: usize = 1 << 21;
const TRIALS: usize = 5;

fn best<F: FnMut() -> usize>(iters: usize, mut f: F) -> u128 {
    let mut b = u128::MAX;
    for _ in 0..TRIALS {
        let t0 = Instant::now();
        let mut cs = 0usize;
        for _ in 0..iters {
            cs ^= f();
        }
        black_box(cs);
        let d = t0.elapsed().as_nanos();
        if d < b {
            b = d;
        }
    }
    b
}

fn mibps(size: usize, iters: usize, nanos: u128) -> f64 {
    (size * iters) as f64 / (1u64 << 20) as f64 / (nanos as f64 / 1e9)
}

fn main() {
    // Deterministic pseudo-random fill; base64 has no data-dependent control flow.
    let mut state: u64 = 0x243F6A8885A308D3;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state as u8
    };
    for &size in &SIZES {
        let data: Vec<u8> = (0..size).map(|_| next()).collect();
        let encoded = STANDARD.encode(&data);
        let iters = std::cmp::max(3, WORK / size);
        best(1, || STANDARD.encode(&data).len());
        best(1, || STANDARD.decode(&encoded).unwrap().len());
        let en = best(iters, || black_box(STANDARD.encode(black_box(&data))).len());
        let dn = best(iters, || black_box(STANDARD.decode(black_box(&encoded)).unwrap()).len());
        println!(
            "rust,{},{:.2},{:.2}",
            size,
            mibps(size, iters, en),
            mibps(size, iters, dn)
        );
    }
}
