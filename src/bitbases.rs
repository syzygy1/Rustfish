// SPDX-License-Identifier: GPL-3.0-or-later

use bitboard::*;
use types::*;

// There are 24 possible pawn squares: the first 4 files and ranks from 2 to 7
const MAX_INDEX: usize = 2*24*64*64;

// Each u32 stores results of 32 positions, one per bit
static mut KPK_BITBASE: [u32; MAX_INDEX / 32] = [0; MAX_INDEX / 32];

// A KPK bitbase index is an integer in [0, IndexMax] range
//
// Information is mapped in a way that minimizes the number of iterations:
//
// bit  0- 5: white king square (from A1 to H8)
// bit  6-11: black king square (from A1 to H8)
// bit    12: side to move (WHITE or BLACK)
// bit 13-14: white pawn file (from FILE_A to FILE_D)
// bit 15-17: white pawn RANK_7 - rank
//            (from RANK_7 - RANK_7 to RANK_7 - RANK_2)
fn index(us: Color, bksq: Square, wksq: Square, psq: Square) -> usize {
    (wksq.0 | (bksq.0 << 6) | (us.0 << 12) | (psq.file() << 13) | ((RANK_7 - psq.rank()) << 15)) as usize
}

const INVALID: u8 = 0;
const UNKNOWN: u8 = 1;
const DRAW   : u8 = 2;
const WIN    : u8 = 4;

struct KPKPosition {
    us: Color,
    ksq: [Square; 2],
    psq: Square,
    result: u8
}

impl KPKPosition {
    fn new(idx: u32) -> KPKPosition {
        let ksq = [ Square((idx >> 0) & 0x3f), Square((idx >> 6) & 0x3f) ];
        let us = Color((idx >> 12) & 0x01);
        let psq =
            Square::make((idx >> 13) & 0x03, RANK_7 - ((idx >> 15) & 0x07));
        let result;

        // Check if two pieces are on the same square or if a king can be
        // captured
        if Square::distance(ksq[WHITE.0 as usize], ksq[BLACK.0 as usize]) <= 1
            || ksq[WHITE.0 as usize] == psq
            || ksq[BLACK.0 as usize] == psq
            || (us == WHITE
                && pawn_attacks(WHITE, psq) & ksq[BLACK.0 as usize] != 0)
        {
            result = INVALID;
        }

        // Immediate win if a pawn can be promoted without getting captured
        else if us == WHITE
            && psq.rank() == RANK_7
            && ksq[us.0 as usize] != psq + NORTH
            && (Square::distance(ksq[(!us).0 as usize], psq + NORTH) > 1
              || pseudo_attacks(KING, ksq[us.0 as usize]) & (psq + NORTH) != 0)
        {
            result = WIN;
        }

        // Immediate draw if it is a stalemate or a king captures undefended
        // pawn
        else if us == BLACK
            && ((pseudo_attacks(KING, ksq[us.0 as usize])
                & !(pseudo_attacks(KING, ksq[(!us).0 as usize])
                    | pawn_attacks(!us, psq))) == 0
                || pseudo_attacks(KING, ksq[us.0 as usize])
                    & psq & !pseudo_attacks(KING, ksq[(!us).0 as usize]) != 0)
        {
            result = DRAW;
        }

        // Position will be classified later
        else {
            result = UNKNOWN;
        }

        KPKPosition { us, ksq, psq, result }
    }

    fn classify(&self, db: &Vec<KPKPosition>) -> u8 {
        // White to move: if one move leads to a position classified as WIN,
        // the result of the current position is WIN; if all moves lead to
        // positions classified as DRAW, the current position is classified
        // as DRAW; otherwise, the current position is classified as UNKNOWN.
        //
        // Black to move: if one move leads to a position classified as DRAW,
        // the result of the current position is DRAW; if all moves lead to
        // positions classified as WIN, the position is classified as WIN;
        // otherwise, the current current position is classified as UNKNOWN.

        let us = self.us;
        let psq = self.psq;

        let them = if us == WHITE { BLACK } else { WHITE };
        let good = if us == WHITE { WIN   } else { DRAW  };
        let bad  = if us == WHITE { DRAW  } else { WIN   };

        let mut r = INVALID;

        for s in pseudo_attacks(KING, self.ksq[us.0 as usize]) {
            r |= if us == WHITE {
                db[index(them, self.ksq[them.0 as usize], s, psq)].result
            } else {
                db[index(them, s, self.ksq[them.0 as usize], psq)].result
            };
        }

        if us == WHITE {
            if psq.rank() < RANK_7 {
                r |= db[index(them, self.ksq[them.0 as usize],
                        self.ksq[us.0 as usize], psq + NORTH)].result;
            }

            if psq.rank() == RANK_2
                && psq + NORTH != self.ksq[us.0 as usize]
                && psq + NORTH != self.ksq[them.0 as usize]
            {
                r |= db[index(them, self.ksq[them.0 as usize],
                        self.ksq[us.0 as usize], psq + 2 * NORTH)].result;
            }
        }

        if r & good != 0 { good }
        else if r & UNKNOWN != 0 { UNKNOWN }
        else { bad }
    }
}

pub fn init() {
    let mut db: Vec<KPKPosition> = Vec::with_capacity(MAX_INDEX);

    // Initialize db with known win/draw positions
    for idx in 0..MAX_INDEX {
        db.push(KPKPosition::new(idx as u32));
    }

    let mut repeat = true;

    // Iterate through the positions until none of the unknown positions can
    // be changed to either wins or draws (15 cycles needed).
    while repeat {
        repeat = false;
        for idx in 0..MAX_INDEX {
            if db[idx].result == UNKNOWN {
                let result = db[idx].classify(&db);
                if result != UNKNOWN {
                    db[idx].result = result;
                    repeat = true;
                }
            }
        }
    }

    // Map 32 results into one KPK_BITBASE[] entry
    for idx in 0..MAX_INDEX {
        if db[idx].result == WIN {
            unsafe {
                KPK_BITBASE[idx / 32] |= 1u32 << (idx & 0x1f);
            }
        }
    }
}

pub fn probe(wksq: Square, wpsq: Square, bksq: Square, us: Color) -> bool {
    debug_assert!(wpsq.file() <= FILE_D);

    let idx = index(us, bksq, wksq, wpsq);
    unsafe { KPK_BITBASE[idx / 32] & (1 << (idx & 0x1f)) != 0 }
}
