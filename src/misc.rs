// SPDX-License-Identifier: GPL-3.0-or-later

#[derive(Clone, Copy)]
pub struct Prng(u64);

// xorshift64star Pseudo-Random Number Generator
// This class is based on original code written and dedicated
// to the public domain by Sebastiano Vigna (2014).
// It has the following characteristics:
//
//  -  Outputs 64-bit numbers
//  -  Passes Dieharder and SmallCrush test batteries
//  -  Does not require warm-up, no zeroland to escape
//  -  Internal state is a single 64-bit integer
//  -  Period is 2^64 - 1
//  -  Speed: 1.60 ns/call (Core i7 @3.40GHz)
//
// For further analysis see
//   <http://vigna.di.unimi.it/ftp/papers/xorshift.pdf>

impl Prng {
    pub fn new(seed: u64) -> Prng {
        Prng(seed)
    }

    pub fn rand64(&mut self) -> u64 {
        (*self).0 ^= (*self).0 >> 12;
        (*self).0 ^= (*self).0 << 25;
        (*self).0 ^= (*self).0 >> 27;
        u64::wrapping_mul(self.0, 2685821657736338717)
    }
}

pub fn engine_info(to_uci: bool) -> String {
//    let months = &"Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec";

    format!("Rustfish 9{}",
        if to_uci {
            "\nid author T. Romstad, M. Costalba, J. Kiiski, G. Linscott"
        } else {
            " by Syzygy based on Stockfish"
        })
}

