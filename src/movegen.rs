// SPDX-License-Identifier: GPL-3.0-or-later

use types::*;
use bitboard::*;
use position::Position;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum GenType {
    Captures,
    Quiets,
    QuietChecks,
    Evasions,
    NonEvasions,
    Legal,
}

use movegen::GenType::*;

#[derive(Clone, Copy)]
pub struct ExtMove {
    pub m: Move,
    pub value: i32,
}

// The MoveList struct is a simple wrapper around generate_*(). It sometimes
// comes in handy to use this struct instead of the low-level generate_*()
// functions.
pub struct MoveList {
    list: [ExtMove; MAX_MOVES],
    idx: usize,
    num: usize,
}

impl MoveList {
    pub fn new(pos: &Position, gen_type: GenType) -> MoveList {
        let mut moves = MoveList {
            list: [ExtMove { m : Move::NONE, value: 0 }; MAX_MOVES],
            idx: 0,
            num: 0,
        };
        { // we need to borrow "moves"
            let mut list: &mut [ExtMove] = &mut moves.list;
            moves.num = match gen_type {
                Captures => generate_captures(pos, &mut list, 0),
                Quiets => generate_quiets(pos, &mut list, 0),
                QuietChecks => generate_quiet_checks(pos, &mut list, 0),
                Evasions => generate_evasions(pos, &mut list, 0),
                NonEvasions => generate_non_evasions(pos, &mut list, 0),
                Legal => generate_legal(pos, &mut list, 0),
            };
            moves.idx = 0;
        } // borrow ends here, so we can move out "moves"
        moves
    }

    pub fn size(&self) -> usize {
        self.num
    }

    pub fn contains(&self, m: Move) -> bool {
        let mut i = 0;
        while i < self.num {
            if self.list[i].m == m {
                return true;
            }
            i += 1;
        }
        return false
    }
}

impl Iterator for MoveList {
    type Item = Move;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.num {
            None
        } else {
            self.idx += 1;
            Some(self.list[self.idx - 1].m)
        }
    }
}

fn generate_castling(
    pos: &Position, list: &mut [ExtMove], idx: usize, us: Color,
    cr: CastlingRight, checks: bool, chess960: bool
) -> usize {
    let king_side = cr == WHITE_OO || cr == BLACK_OO;

    if pos.castling_impeded(cr) || !pos.has_castling_right(cr) {
        return idx;
    }

    // After castling, the rook and king final positions are the same in
    // Chess960 as they are in standard chess.
    let kfrom = pos.square(us, KING);
    let rfrom = pos.castling_rook_square(cr);
    let kto =
        relative_square(us, if king_side { Square::G1 } else { Square::C1 });
    let enemies = pos.pieces_c(!us);

    debug_assert!(pos.checkers() == 0);

    let direction = match chess960 {
        true  => if kto > kfrom { WEST } else { EAST },
        false => if king_side { WEST } else { EAST },
    };

    let mut s = kto;
    while s != kfrom {
        if pos.attackers_to(s) & enemies != 0 {
            return idx;
        }
        s += direction;
    }

    // Because we generate only legal castling moves, we need to verify that
    // when moving the castling rook we do not discover some hidden checker.
    // For instance an enemy queen on A1 when the castling rook is on B1.
    if chess960
        && attacks_bb(ROOK, kto, pos.pieces() ^ rfrom)
            & pos.pieces_cpp(!us, ROOK, QUEEN) != 0
    {
        return idx;
    }

    let m = Move::make_special(CASTLING, kfrom, rfrom);

    if checks && !pos.gives_check(m) {
        return idx;
    }

    list[idx].m = m;
    idx + 1
}

fn add_promotions(
    list: &mut [ExtMove], mut idx: usize, to: Square, ksq: Square,
    gen_type: GenType, direction: Direction
) -> usize {
    if gen_type == Captures || gen_type == Evasions || gen_type == NonEvasions {
        list[idx].m = Move::make_prom(to - direction, to, QUEEN);
        idx += 1;
    }

    if gen_type == Quiets || gen_type == Evasions || gen_type == NonEvasions {
        list[idx    ].m = Move::make_prom(to - direction, to, ROOK);
        list[idx + 1].m = Move::make_prom(to - direction, to, BISHOP);
        list[idx + 2].m = Move::make_prom(to - direction, to, KNIGHT);
        idx += 3;
    }

    // Knight promotion is the only promotion that can give a direct check
    // that's not already included in the queen promotion.
    if gen_type == QuietChecks && pseudo_attacks(KNIGHT, to) & ksq != 0 {
        list[idx].m = Move::make_prom(to - direction, to, KNIGHT);
        idx += 1;
    }

    idx
}

fn generate_pawn_moves(
    pos: &Position, list: &mut [ExtMove], mut idx: usize, target: Bitboard,
    us: Color, gen_type: GenType
) -> usize {
    let them = !us;
    let trank_8bb = if us == WHITE { RANK8_BB } else { RANK1_BB };
    let trank_7bb = if us == WHITE { RANK7_BB } else { RANK2_BB };
    let trank_3bb = if us == WHITE { RANK3_BB } else { RANK6_BB };
    let up    = if us == WHITE { NORTH      } else { SOUTH      };
    let right = if us == WHITE { NORTH_EAST } else { SOUTH_WEST };
    let left  = if us == WHITE { NORTH_WEST } else { SOUTH_EAST };

    let mut empty_squares = Bitboard(0);

    let pawns_on_7     = pos.pieces_cp(us, PAWN) &  trank_7bb; 
    let pawns_not_on_7 = pos.pieces_cp(us, PAWN) & !trank_7bb;

    let enemies = match gen_type {
        Evasions => pos.pieces_c(them) & target,
        Captures => target,
        _        => pos.pieces_c(them)
    };

    // Single and double pawn pushes, no promotions
    if gen_type != Captures {
        empty_squares =
            if gen_type == Quiets || gen_type == QuietChecks {
                target
            } else {
                !pos.pieces()
            };

        let mut b1 = pawns_not_on_7.shift(up) & empty_squares;
        let mut b2 = (b1 & trank_3bb).shift(up) & empty_squares;

        if gen_type == Evasions { // Consider only blocking squares
            b1 &= target;
            b2 &= target;
        }

        if gen_type == QuietChecks {
            let ksq = pos.square(them, KING);

            b1 &= pos.attacks_from_pawn(ksq, them);
            b2 &= pos.attacks_from_pawn(ksq, them);

            // Add pawn pushes which give discovered check. This is possible
            // only if the pawn is not on the same file as the enemy king,
            // because we don't generate captures. Note that a possible
            // discovery check promotion has already been generated together
            // with the captures.
            let dc_candidates = pos.discovered_check_candidates();
            if pawns_not_on_7 & dc_candidates != 0 {
                let dc1 =
                    (pawns_not_on_7 & dc_candidates).shift(up)
                    & empty_squares
                    & !file_bb(ksq.file());
                let dc2 = (dc1 & trank_3bb).shift(up) & empty_squares;

                b1 |= dc1;
                b2 |= dc2;
            }
        }

        for to in b1 {
            list[idx].m = Move::make(to - up, to);
            idx += 1;
        }

        for to in b2 {
            list[idx].m = Move::make(to - up - up, to);
            idx += 1;
        }
    }

    // Promotions and underpromotions
    if pawns_on_7 != 0 && (gen_type != Evasions || target & trank_8bb != 0) {
        if gen_type == Captures {
            empty_squares = !pos.pieces();
        }

        if gen_type == Evasions {
            empty_squares &= target;
        }

        let b1 = pawns_on_7.shift(right) & enemies;
        let b2 = pawns_on_7.shift(left ) & enemies;
        let b3 = pawns_on_7.shift(up   ) & empty_squares;

        let ksq = pos.square(them, KING);

        for s in b1 {
            idx = add_promotions(list, idx, s, ksq, gen_type, right);
        }

        for s in b2 {
            idx = add_promotions(list, idx, s, ksq, gen_type, left);
        }

        for s in b3 {
            idx = add_promotions(list, idx, s, ksq, gen_type, up);
        }
    }

    // Standard and en-passant captures
    if gen_type == Captures || gen_type == Evasions || gen_type == NonEvasions {
        let b1 = pawns_not_on_7.shift(right) & enemies;
        let b2 = pawns_not_on_7.shift(left ) & enemies;

        for to in b1 {
            list[idx].m = Move::make(to - right, to);
            idx += 1;
        }

        for to in b2 {
            list[idx].m = Move::make(to - left, to);
            idx += 1;
        }

        if pos.ep_square() != Square::NONE {
            debug_assert!(pos.ep_square().rank() == relative_rank(us, RANK_6));

            // An en passant capture can be an evasion only if the checking
            // piece is the double pushed pawn and so is in the target.
            // Otherwise this is a discovery check and we are forced to do
            // otherwise.
            if gen_type == Evasions && target & (pos.ep_square() - up) == 0 {
                return idx;
            }

            let b1 =
                pawns_not_on_7 & pos.attacks_from_pawn(pos.ep_square(), them);

            debug_assert!(b1 != 0);

            for to in b1 {
                list[idx].m =
                    Move::make_special(ENPASSANT, to, pos.ep_square());
                idx += 1;
            }
        }
    }

    idx
}

fn generate_moves(
    pos: &Position, list: &mut [ExtMove], mut idx: usize, us: Color,
    target: Bitboard, pt: PieceType, checks: bool
) -> usize {
    debug_assert!(pt != KING && pt != PAWN);

    for from in pos.square_list(us, pt) {
        if checks {
            if (pt == BISHOP || pt == ROOK || pt == QUEEN)
                && pseudo_attacks(pt, from) & target
                    & pos.check_squares(pt) == 0
            {
                continue;
            }

            if pos.discovered_check_candidates() & from != 0 {
                continue;
            }
        }

        let mut b = pos.attacks_from(pt, from) & target;

        if checks {
            b &= pos.check_squares(pt);
        }

        for to in b {
            list[idx].m = Move::make(from, to);
            idx += 1;
        }
    }

    idx
}

fn generate_all(
    pos: &Position, list: &mut [ExtMove], mut idx: usize, target: Bitboard,
    us: Color, gen_type: GenType
) -> usize {
    let checks = gen_type == QuietChecks;

    idx = generate_pawn_moves(pos, list, idx, target, us, gen_type);
    idx = generate_moves(pos, list, idx, us, target, KNIGHT, checks);
    idx = generate_moves(pos, list, idx, us, target, BISHOP, checks);
    idx = generate_moves(pos, list, idx, us, target, ROOK  , checks);
    idx = generate_moves(pos, list, idx, us, target, QUEEN , checks);

    if gen_type != QuietChecks && gen_type != Evasions {
        let ksq = pos.square(us, KING);
        let b = pos.attacks_from(KING, ksq) & target;
        for to in b {
            list[idx].m = Move::make(ksq, to);
            idx += 1;
        }
    }

    if gen_type != Captures && gen_type != Evasions && pos.can_castle(us) {
        if pos.is_chess960() {
            idx = generate_castling(pos, list, idx, us,
                CastlingRight::make(us, CastlingSide::KING), checks, true);
            idx = generate_castling(pos, list, idx, us,
                CastlingRight::make(us, CastlingSide::QUEEN), checks, true);
        } else {
            idx = generate_castling(pos, list, idx, us,
                CastlingRight::make(us, CastlingSide::KING), checks, false);
            idx = generate_castling(pos, list, idx, us,
                CastlingRight::make(us, CastlingSide::QUEEN), checks, false);
        }
    }

    idx
}

fn generate(
    pos: &Position, list: &mut [ExtMove], idx: usize, gen_type: GenType
) -> usize {
    debug_assert!(
        gen_type == Captures || gen_type == Quiets || gen_type == NonEvasions
    );
    debug_assert!(pos.checkers() == 0);

    let us = pos.side_to_move();

    let target = match gen_type {
        Captures    => pos.pieces_c(!us),
        Quiets      => !pos.pieces(),
        NonEvasions => !pos.pieces_c(us),
        _           => Bitboard(0)
    };

    if us == WHITE {
        generate_all(pos, list, idx, target, WHITE, gen_type)
    } else {
        generate_all(pos, list, idx, target, BLACK, gen_type)
    }
}

// generate_captures() generates all pseudo-legal captures and queen
// promotions
pub fn generate_captures(
    pos: &Position, list: &mut [ExtMove], idx: usize
) -> usize {
    generate(pos, list, idx, Captures)
}

// generate_quiets() generates all pseudo-legal non-captures and
// underpromotions.
pub fn generate_quiets(
    pos: &Position, list: &mut [ExtMove], idx: usize
) -> usize {
    generate(pos, list, idx, Quiets)
}

// generate_non_evasions() generates all pseudo-legal captures and
// non-captures
pub fn generate_non_evasions(
    pos: &Position, list: &mut [ExtMove], idx: usize
) -> usize {
    generate(pos, list, idx, NonEvasions)
}

// generate_quiet_checks() generates all pseudo-legal non-captures and
// knight underpromotions that give check
pub fn generate_quiet_checks(
    pos: &Position, list: &mut [ExtMove], mut idx: usize
) -> usize {
    debug_assert!(pos.checkers() == 0);

    let us = pos.side_to_move();
    let dc = pos.discovered_check_candidates();

    for from in dc {
        let pt = pos.piece_on(from).piece_type();

        if pt == PAWN {
            continue; // Will be generated together with direct checks
        }

        let mut b = pos.attacks_from(pt, from) & !pos.pieces();

        if pt == KING {
            b &= !pseudo_attacks(QUEEN, pos.square(!us, KING));
        }

        for to in b {
            list[idx].m = Move::make(from, to);
            idx += 1;
        }
    }

    if us == WHITE {
        generate_all(pos, list, idx, !pos.pieces(), WHITE, QuietChecks)
    } else {
        generate_all(pos, list, idx, !pos.pieces(), BLACK, QuietChecks)
    }
}

// generate_evasions() generates all pseudo-legal check evasions when the
// side to move is in check
pub fn generate_evasions(
    pos: &Position, list: &mut [ExtMove], mut idx: usize
) -> usize {
    debug_assert!(pos.checkers() != 0);

    let us = pos.side_to_move();
    let ksq = pos.square(us, KING);
    let mut slider_attacks = Bitboard(0);
    let sliders = pos.checkers() & !pos.pieces_pp(KNIGHT, PAWN);

    // Find all the squares attacked by slider checks. We will remove them
    // from the king evasions in order to skip known illegal moves, which
    // avoids any useless legality checks later on.
    for check_sq in sliders {
        slider_attacks |= line_bb(check_sq, ksq) ^ check_sq;
    }

    // Generate evasions for king, capture and non-capture moves
    let b = pos.attacks_from(KING, ksq) & !pos.pieces_c(us) & !slider_attacks;
    for to in b {
        list[idx].m = Move::make(ksq, to);
        idx += 1;
    }

    if more_than_one(pos.checkers()) {
        return idx; // Double check, only a king move can save the day
    }

    // Generate blocking evasions or captures of the checking piece
    let check_sq = lsb(pos.checkers());
    let target = between_bb(check_sq, ksq) | check_sq;

    if us == WHITE {
        generate_all(pos, list, idx, target, WHITE, Evasions)
    } else {
        generate_all(pos, list, idx, target, BLACK, Evasions)
    }
}

// generate_legal() generates all the legal moves in the given position
pub fn generate_legal(
    pos: &Position, list: &mut [ExtMove], idx: usize
) -> usize {
    let pinned = pos.pinned_pieces(pos.side_to_move()) != 0;
    let ksq = pos.square(pos.side_to_move(), KING);

    let pseudo = if pos.checkers() != 0 {
        generate_evasions(pos, list, idx)
    } else {
        generate_non_evasions(pos, list, idx)
    };

    let mut legal = idx;
    for i in idx..pseudo {
        let m = list[i].m;
        if (!pinned && m.from() != ksq && m.move_type() != ENPASSANT)
            || pos.legal(m)
        {
            list[legal].m = m;
            legal += 1;
        }
    }

    legal
}
