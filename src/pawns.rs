// SPDX-License-Identifier: GPL-3.0-or-later

use bitboard::*;
use position::Position;
use types::*;

use std;

macro_rules! V { ($x:expr) => (Value($x)) }
macro_rules! S { ($x:expr, $y:expr) => (Score(($y << 16) + $x)) }

const V0: Value = Value::ZERO;

// Isolated pawn penalty
const ISOLATED: Score = S!(13, 18);

// Backward pawn penalty
const BACKWARD: Score = S!(24, 12);

// Connected pawn bonus by opposed, phalanx, #support and rank
static mut CONNECTED: [[[[Score; 8]; 3]; 2]; 2] =
    [[[[Score::ZERO; 8]; 3]; 2]; 2];

// Doubled pawn penalty
const DOUBLED: Score = S!(18, 38);

// Lever bonus by rank
const LEVER: [Score; 8] = [
    S!( 0,  0), S!( 0,  0), S!(0, 0), S!(0, 0),
    S!(17, 16), S!(33, 32), S!(0, 0), S!(0, 0)
];

// Weakness of our pawn shelter in front of the king by
// [is_king_file][distance from edge][rank]. RANK_1 = 0 is used for files
// where we have no pawns or our pawn is behind our king.
const SHELTER_WEAKNESS: [[[Value; 8]; 4]; 2] = [
    [ [ V!( 97), V!(17), V!( 9), V!(44), V!( 84), V!( 87), V!( 99), V0 ],
      [ V!(106), V!( 6), V!(33), V!(86), V!( 87), V!(104), V!(112), V0 ],
      [ V!(101), V!( 2), V!(65), V!(98), V!( 58), V!( 89), V!(115), V0 ],
      [ V!( 73), V!( 7), V!(54), V!(73), V!( 84), V!( 83), V!(111), V0 ] ],
    [ [ V!(104), V!(20), V!( 6), V!(27), V!( 86), V!( 93), V!( 82), V0 ],
      [ V!(123), V!( 9), V!(34), V!(96), V!(112), V!( 88), V!( 75), V0 ],
      [ V!(120), V!(25), V!(65), V!(91), V!( 66), V!( 78), V!(117), V0 ],
      [ V!( 81), V!( 2), V!(47), V!(63), V!( 94), V!( 93), V!(104), V0 ] ],
];

// Danger of enemy pawns moving toward our king by
// [type][distance from edge][rank]. For the unopposed and unblocked cases,
// RANK_1 = 0 is used when opponent has no pawn on the given file or their
// pawn is behind our king.
const STORM_DANGER: [[[Value; 8]; 4]; 4] = [
    // BlockedByKing
    [ [ V!( 0),  V!(-290), V!(-274), V!(57), V!(41), V0, V0, V0 ],
      [ V!( 0),  V!(  60), V!( 144), V!(39), V!(13), V0, V0, V0 ],
      [ V!( 0),  V!(  65), V!( 141), V!(41), V!(34), V0, V0, V0 ],
      [ V!( 0),  V!(  53), V!( 127), V!(56), V!(14), V0, V0, V0 ] ],
    // Unopposed
    [ [ V!( 4),  V!(  73), V!( 132), V!(46), V!(31), V0, V0, V0 ],
      [ V!( 1),  V!(  64), V!( 143), V!(26), V!(13), V0, V0, V0 ],
      [ V!( 1),  V!(  47), V!( 110), V!(44), V!(24), V0, V0, V0 ],
      [ V!( 0),  V!(  72), V!( 127), V!(50), V!(31), V0, V0, V0 ] ],
    // BlockedByPawn
    [ [ V!( 0),  V!(   0), V!(  79), V!(23), V!( 1), V0, V0, V0 ],
      [ V!( 0),  V!(   0), V!( 148), V!(27), V!( 2), V0, V0, V0 ],
      [ V!( 0),  V!(   0), V!( 161), V!(16), V!( 1), V0, V0, V0 ],
      [ V!( 0),  V!(   0), V!( 171), V!(22), V!(15), V0, V0, V0 ] ],
    // Unblocked
    [ [ V!(22),  V!(  45), V!( 104), V!(62), V!( 6), V0, V0, V0 ],
      [ V!(31),  V!(  30), V!(  99), V!(39), V!(19), V0, V0, V0 ],
      [ V!(23),  V!(  29), V!(  96), V!(41), V!(15), V0, V0, V0 ],
      [ V!(21),  V!(  23), V!( 116), V!(41), V!(15), V0, V0, V0 ] ],
];

// Max bonus for king safety. Corresponds to start position with all the
// pawns in front of the king and no enemy pawns on the horizon.
const MAX_SAFETY_BONUS: Value = V!(258);

// pawns::Entry contains various information about a pawn structure. A lookup
// in the pawn hash table (performed by calling the probing function) returns
// a pointer to an Entry object.

pub struct Entry {
    key: Key,
    score: Score,
    passed_pawns: [Bitboard; 2],
    pawn_attacks: [Bitboard; 2],
    pawn_attacks_span: [Bitboard; 2],
    king_squares: [Square; 2],
    king_safety: [Score; 2],
    weak_unopposed: [i32; 2],
    castling_rights: [CastlingRight; 2],
    semiopen_files: [i32; 2],
    pawns_on_squares: [[i32; 2]; 2],
    asymmetry: i32,
    open_files: i32,
}

impl Entry {
    pub fn new() -> Entry {
        Entry {
            key: Key(0),
            score: Score::ZERO,
            passed_pawns: [Bitboard(0); 2],
            pawn_attacks: [Bitboard(0); 2],
            pawn_attacks_span: [Bitboard(0); 2],
            king_squares: [Square(0); 2],
            king_safety: [Score::ZERO; 2],
            weak_unopposed: [0; 2],
            castling_rights: [CastlingRight(0); 2],
            semiopen_files: [0; 2],
            pawns_on_squares: [[0; 2]; 2], // [Color][light/dark squares]
            asymmetry: 0,
            open_files: 0,
        }
    }

    pub fn pawns_score(&self) -> Score {
        self.score
    }

    pub fn pawn_attacks(&self, c: Color) -> Bitboard {
        self.pawn_attacks[c.0 as usize]
    }

    pub fn passed_pawns(&self, c: Color) -> Bitboard {
        self.passed_pawns[c.0 as usize]
    }

    pub fn pawn_attacks_span(&self, c: Color) -> Bitboard {
        self.pawn_attacks_span[c.0 as usize]
    }

    pub fn weak_unopposed(&self, c: Color) -> i32 {
        self.weak_unopposed[c.0 as usize]
    }

    pub fn pawn_asymmetry(&self) -> i32 {
        self.asymmetry
    }

    pub fn open_files(&self) -> i32 {
        self.open_files
    }

    pub fn semiopen_file(&self, c: Color, f: File) -> i32 {
        self.semiopen_files[c.0 as usize] & (1 << f)
    }

    pub fn semiopen_side(&self, c: Color, f: File, left_side: bool) -> i32 {
        self.semiopen_files[c.0 as usize]
        & (if left_side { (1 << f) - 1 } else { !((1 << (f + 1)) - 1) })
    }

    pub fn pawns_on_same_color_squares(&self, c: Color, s: Square) -> i32 {
        self.pawns_on_squares[c.0 as usize][((DARK_SQUARES & s) != 0) as usize]
    }

    pub fn king_safety<C: ColorTrait>(
        &mut self, pos: &Position, ksq: Square
    ) -> Score {
        let us = C::color();
        if self.king_squares[us.0 as usize] != ksq
            || self.castling_rights[us.0 as usize] != pos.castling_rights(us)
        {
            self.king_safety[us.0 as usize] =
                self.do_king_safety::<C>(pos, ksq);
        }
        self.king_safety[us.0 as usize]
    }

    // shelter_storm() calculates shelter and storm penalties for the file
    // the king is on, as well as the two closest files.

    fn shelter_storm<C: ColorTrait>(
        &self, pos: &Position, ksq: Square
    ) -> Value {
        let us = C::color();
        let them = if us == WHITE { BLACK} else { WHITE };

        const BLOCKED_BY_KING: usize = 0;
        const UNOPPOSED: usize = 1;
        const BLOCKED_BY_PAWN: usize = 2;
        const UNBLOCKED: usize = 3;

        let b = pos.pieces_p(PAWN)
            & (forward_ranks_bb(us, ksq) | rank_bb(ksq.rank()));
        let our_pawns = b & pos.pieces_c(us);
        let their_pawns = b & pos.pieces_c(them);
        let mut safety = MAX_SAFETY_BONUS;
        let center = std::cmp::max(FILE_B, std::cmp::min(FILE_G, ksq.file()));

        for f in (center-1)..(center+2) {
            let b = our_pawns & file_bb(f);
            let rk_us = if b != 0 { backmost_sq(us, b).relative_rank(us) }
                        else { RANK_1 };

            let b = their_pawns & file_bb(f);
            let rk_them = if b != 0 { frontmost_sq(them, b).relative_rank(us) }
                          else { RANK_1 };

            let d = std::cmp::min(f, FILE_H - f);
            safety -= SHELTER_WEAKNESS[(f == ksq.file()) as usize][d as usize]
                                                            [rk_us as usize]
                    + STORM_DANGER
                    [if f == ksq.file() && rk_them == ksq.relative_rank(us) + 1
                        { BLOCKED_BY_KING }
                     else if rk_us == RANK_1 { UNOPPOSED }
                     else if rk_them == rk_us + 1 { BLOCKED_BY_PAWN }
                     else { UNBLOCKED }]
                    [d as usize][rk_them as usize];
        }

        safety
    }

    // do_king_safety() calculates a bonus for king safety. It is called only
    // when king square changes, which is in about 20% of total king_safety()
    // calls.

    fn do_king_safety<C: ColorTrait>(
        &mut self, pos: &Position, ksq: Square
    ) -> Score {
        let us = C::color();
        self.king_squares[us.0 as usize] = ksq;
        self.castling_rights[us.0 as usize] = pos.castling_rights(us);
        let mut min_king_pawn_distance = 0i32;

        let pawns = pos.pieces_cp(us, PAWN);
        if pawns != 0 {
            while distance_ring_bb(ksq, min_king_pawn_distance) & pawns == 0 {
                min_king_pawn_distance += 1;
            }
            min_king_pawn_distance += 1;
        }

        let mut bonus = self.shelter_storm::<C>(pos, ksq);

        // If we can castle use the bonus after the castling if it is bigger
        if pos.has_castling_right(us | CastlingSide::KING) {
            bonus = std::cmp::max(bonus,
                self.shelter_storm::<C>(pos, Square::G1.relative(us)));
        }

        if pos.has_castling_right(us | CastlingSide::QUEEN) {
            bonus = std::cmp::max(bonus,
                self.shelter_storm::<C>(pos, Square::C1.relative(us)));
        }

        Score::make(bonus.0, -16 * min_king_pawn_distance)
    }

}

// pawns::init() initializes some tables needed by evaluation.

pub fn init() {
    const SEED: [i32; 8] = [0, 13, 24, 18, 76, 100, 175, 330];

    for opposed in 0..2 {
        for phalanx in 0..2 {
            for support in 0..3 {
                for r in 1..7i32 {
                    let v = 17 * (support as i32) + ((SEED[r as usize] +
                        (if phalanx != 0
                            { (SEED[(r+1) as usize] - SEED[r as usize]) / 2 }
                        else { 0 }))
                        >> opposed);
                    unsafe {
                        CONNECTED[opposed as usize][phalanx as usize]
                                [support as usize][r as usize] =
                                        Score::make(v, v * (r-2) / 4);
                    }
                }
            }
        }
    }
}

// pawns::probe() looks up the current position's pawn configuration in the
// pawn hash table. If it is not found, it is computed and stored in the table.

pub fn probe(pos: &Position) -> &mut Entry {
    let key = pos.pawn_key();
    let e = pos.pawns_table[(key.0 & 16383) as usize].get();
    let e: &'static mut Entry = unsafe { &mut *e };

    if e.key == key {
        return e;
    }

    e.key = key;
    e.score = evaluate::<White>(pos, e) - evaluate::<Black>(pos, e);
    e.asymmetry = (e.semiopen_files[WHITE.0 as usize]
        ^ e.semiopen_files[BLACK.0 as usize]).count_ones() as i32;
    e.open_files = (e.semiopen_files[WHITE.0 as usize]
        & e.semiopen_files[BLACK.0 as usize]).count_ones() as i32;

    e
}

fn evaluate<C: ColorTrait>(pos: &Position, e: &mut Entry) -> Score {
    let us = C::color();
    let them  = if us == WHITE { BLACK } else { WHITE };
    let up    = if us == WHITE { NORTH } else { SOUTH };
    let right = if us == WHITE { NORTH_EAST } else { SOUTH_WEST };
    let left  = if us == WHITE { NORTH_WEST } else { SOUTH_EAST };

    let mut score = Score::ZERO;

    let our_pawns = pos.pieces_cp(us, PAWN);
    let their_pawns = pos.pieces_cp(them, PAWN);

    e.passed_pawns[us.0 as usize] = Bitboard(0);
    e.pawn_attacks_span[us.0 as usize] = Bitboard(0);
    e.weak_unopposed[us.0 as usize] = 0;
    e.semiopen_files[us.0 as usize] = 0xff;
    e.king_squares[us.0 as usize] = Square::NONE;
    e.pawn_attacks[us.0 as usize] =
        our_pawns.shift(right) | our_pawns.shift(left);
    e.pawns_on_squares[us.0 as usize][BLACK.0 as usize] =
        popcount(our_pawns & DARK_SQUARES) as i32;
    e.pawns_on_squares[us.0 as usize][WHITE.0 as usize] =
        popcount(our_pawns & !DARK_SQUARES) as i32;

    // Loop through all pawns of the current color and score each pawn
    for s in pos.square_list(us, PAWN) {
        debug_assert!(pos.piece_on(s) == Piece::make(us, PAWN));

        let f = s.file();

        e.semiopen_files[us.0 as usize] &= !(1 << f);
        e.pawn_attacks_span[us.0 as usize] |= pawn_attack_span(us, s);

        // Flag the pawn
        let opposed    = their_pawns & forward_file_bb(us, s);
        let stoppers   = their_pawns & passed_pawn_mask(us, s);
        let lever      = their_pawns & pawn_attacks(us, s);
        let lever_push = their_pawns & pawn_attacks(us, s + up);
        let doubled    = our_pawns & (s - up);
        let neighbours = our_pawns & adjacent_files_bb(f);
        let phalanx    = neighbours & rank_bb(s.rank());
        let supported  = neighbours & rank_bb((s - up).rank());

        let backward;

        // A pawn is backward if it is behind all pawns of the same color on
        // the adjacent files and cannot be safely advanced.
        if neighbours == 0 || lever != 0 || s.relative_rank(us) >= RANK_5 {
            backward = false;
        } else {
            // Find the backmost rank with neighbours or stoppers
            let b = rank_bb(backmost_sq(us, neighbours | stoppers).rank());

            // The pawn is backward if it cannot safely progress to that
            // rank: either there is a stopper in the way on this rank or
            // there is a stopper on an adjacent file which controls the way
            // to that rank.
            backward =
                (b | (b & adjacent_files_bb(f)).shift(up)) & stoppers != 0;
            debug_assert!(
                !(backward && forward_ranks_bb(them, s + up) & neighbours != 0)
            );
        }

        // Passed pawns will be properly scored in evaluation because we need
        // full attack info to evaluate them. Include also not passed pawns
        // which could become passed after one or two pawn pushes.
        if stoppers ^ lever ^ lever_push == 0
            && our_pawns & forward_file_bb(us, s) == 0
            && popcount(supported) >= popcount(lever)
            && popcount(phalanx) >= popcount(lever_push)
        {
            e.passed_pawns[us.0 as usize] |= s;
        }
        else if stoppers ^ (s + up) == 0
            && s.relative_rank(us) >= RANK_5
        {
            for sq in supported.shift(up) & !their_pawns {
                if !more_than_one(their_pawns & pawn_attacks(us, sq)) {
                    e.passed_pawns[us.0 as usize] |= s;
                }
            }
        }

        // Score this pawn
        if supported | phalanx != 0 {
            score += unsafe {
                CONNECTED[(opposed != 0) as usize][(phalanx != 0) as usize]
                [popcount(supported) as usize][s.relative_rank(us) as usize]
            };
        } else if neighbours == 0 {
            score -= ISOLATED;
            e.weak_unopposed[us.0 as usize] += (opposed == 0) as i32;
        } else if backward {
            score -= BACKWARD;
            e.weak_unopposed[us.0 as usize] += (opposed == 0) as i32;
        }

        if doubled != 0 && supported == 0 {
            score -= DOUBLED;
        }

        if lever != 0 {
            score += LEVER[s.relative_rank(us) as usize];
        }
    }

    score
}
