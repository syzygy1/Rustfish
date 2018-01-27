// SPDX-License-Identifier: GPL-3.0-or-later

use bitboard::*;
use material;
use movegen::*;
use movepick::*;
use pawns;
use psqt;
use search;
use tb;
use threads::ThreadCtrl;
use types::*;
use uci;

use std;
use std::sync::Arc;

pub mod zobrist {
    use types::*;
    use bitboard;
    use misc;

    static mut PSQ: [[Key; 64]; 16] = [[Key(0); 64]; 16];
    static mut ENPASSANT: [Key; 8] = [Key(0); 8];
    static mut CASTLING: [Key; 16] = [Key(0); 16];
    static mut SIDE: Key = Key(0);
    static mut NO_PAWNS: Key = Key(0);

    pub fn psq(pc: Piece, s: Square) -> Key {
        unsafe { PSQ[pc.0 as usize][s.0 as usize] }
    }

    pub fn material(pc: Piece, num: i32) -> Key {
        unsafe { PSQ[pc.0 as usize][num as usize] }
    }

    pub fn enpassant(f: File) -> Key {
        unsafe { ENPASSANT[f as usize] }
    }

    pub fn castling(cr: CastlingRight) -> Key {
        unsafe { CASTLING[cr.0 as usize] }
    }

    pub fn side() -> Key {
        unsafe { SIDE }
    }

    pub fn no_pawns() -> Key {
        unsafe { NO_PAWNS }
    }

    // position::init() initializes at startup the various arrays used to
    // compute hash keys.

    pub fn init() {
        let mut rng = misc::Prng::new(1070372);

        unsafe {
            for i in 1..15 {
                if i != 7 && i != 8 {
                    for s in 0..64 {
                        PSQ[i][s] = Key(rng.rand64());
                    }
                }
            }

            for f in 0..8 {
                ENPASSANT[f] = Key(rng.rand64());
            }

            for cr in 0..16 {
                let b = bitboard::Bitboard(cr);
                for s in b {
                    let k = CASTLING[1usize << s.0];
                    CASTLING[cr as usize] ^=
                        if k.0 != 0 { k } else { Key(rng.rand64()) };
                }
            }

            SIDE = Key(rng.rand64());
            NO_PAWNS = Key(rng.rand64());
        }
    }
}

#[derive(Clone)]
pub struct StateInfo {
    // Copied when making a move
    pub pawn_key: Key,
    pub material_key: Key,
    pub non_pawn_material: [Value; 2],
    pub castling_rights: CastlingRight,
    pub rule50: i32,
    pub plies_from_null: i32,
    pub psq: Score,
    pub ep_square: Square,

    // Not copied when making a move (will be recomputed anyhow)
    pub key: Key,
    pub checkers_bb: Bitboard,
    pub captured_piece: Piece,
    pub blockers_for_king: [Bitboard; 2],
    pub pinners_for_king: [Bitboard; 2],
    pub check_squares: [Bitboard; 8],
}

impl StateInfo {
    pub fn new() -> StateInfo {
        StateInfo {
            pawn_key: Key(0),
            material_key: Key(0),
            non_pawn_material: [Value::ZERO; 2],
            castling_rights: CastlingRight(0),
            rule50: 0,
            plies_from_null: 0,
            psq: Score::ZERO,
            ep_square: Square::NONE,
            key: Key(0),
            checkers_bb: Bitboard(0),
            captured_piece: NO_PIECE,
            blockers_for_king: [Bitboard(0); 2],
            pinners_for_king: [Bitboard(0); 2],
            check_squares: [Bitboard(0); 8],
        }
    }

    pub fn copy(&self) -> StateInfo {
        StateInfo {
            pawn_key: self.pawn_key,
            material_key: self.material_key,
            non_pawn_material: self.non_pawn_material,
            castling_rights: self.castling_rights,
            rule50: self.rule50,
            plies_from_null: self.plies_from_null,
            psq: self.psq,
            ep_square: self.ep_square,
            key: Key(0),
            checkers_bb: Bitboard(0),
            captured_piece: NO_PIECE,
            blockers_for_king: [Bitboard(0); 2],
            pinners_for_king: [Bitboard(0); 2],
            check_squares: [Bitboard(0); 8],
        }
    }
}

pub struct Position {
    board: [Piece; 64],
    by_color_bb: [Bitboard; 2],
    by_type_bb: [Bitboard; 8],
    piece_count: [i32; 16],
    piece_list: [[Square; 16]; 16],
    index: [i32; 64],
    castling_rights_mask: [CastlingRight; 64],
    castling_rook_square: [Square; 16],
    castling_path: [Bitboard; 16],
    game_ply: i32,
    side_to_move: Color,
    states: Vec<StateInfo>,
    chess960: bool,
    // Thread variables from here
    // only for main thread:
    pub failed_low: bool,
    pub best_move_changes: f64,
    pub previous_time_reduction: f64,
    pub previous_score: Value,
    pub calls_cnt: i32,
    // for all threads:
    pub thread_ctrl: Option<Arc<ThreadCtrl>>,
    pub is_main: bool,
    pub thread_idx: i32,
    pub pv_idx: usize,
    pub pv_last: usize,
    pub sel_depth: i32,
    pub nmp_ply: i32,
    pub nmp_odd: i32,
    pub nodes: u64,
    pub tb_hits: u64,
    pub completed_depth: Depth,
    pub root_moves: search::RootMoves,
    // thread-specific tables
    pub pawns_table: Vec<std::cell::UnsafeCell<pawns::Entry>>,
    pub material_table: Vec<std::cell::UnsafeCell<material::Entry>>,
    pub counter_moves: CounterMoveHistory,
    pub main_history: ButterflyHistory,
    pub capture_history: CapturePieceToHistory,
    pub cont_history: ContinuationHistory,
}

impl Position {
    pub fn new() -> Position {
        Position {
            board: [NO_PIECE; 64],
            by_color_bb: [Bitboard(0); 2],
            by_type_bb: [Bitboard(0); 8],
            piece_count: [0; 16],
            piece_list: [[Square::NONE; 16]; 16],
            index: [0; 64],
            castling_rights_mask: [CastlingRight(0); 64],
            castling_rook_square: [Square::NONE; 16],
            castling_path: [Bitboard(0); 16],
            game_ply: 0,
            side_to_move: WHITE,
            states: Vec::new(),
            chess960: false,
            failed_low: false,
            best_move_changes: 0.0,
            previous_time_reduction: 0.0,
            previous_score: Value::ZERO,
            calls_cnt: 0,
            thread_ctrl: None,
            is_main: false,
            thread_idx: 0,
            pv_idx: 0,
            pv_last: 0,
            sel_depth: 0,
            nmp_ply: 0,
            nmp_odd: 0,
            nodes: 0,
            tb_hits: 0,
            completed_depth: Depth::ZERO,
            root_moves: Vec::new(),
            pawns_table: Vec::new(),
            material_table: Vec::new(),
            counter_moves: unsafe { std::mem::zeroed() },
            main_history: unsafe { std::mem::zeroed() },
            capture_history: unsafe { std::mem::zeroed() },
            cont_history: unsafe { std::mem::zeroed() },
        }
    }

    pub fn init_states(&mut self) {
        self.states.truncate(0);
        self.states.push(StateInfo::new());
    }

    fn st(&self) -> &StateInfo {
        self.states.last().unwrap()
    }

    fn st_mut(&mut self) -> &mut StateInfo {
        self.states.last_mut().unwrap()
    }

    pub fn side_to_move(&self) -> Color {
        self.side_to_move
    }

    pub fn empty(&self, s: Square) -> bool {
        self.board[s.0 as usize] == NO_PIECE
    }

    pub fn piece_on(&self, s: Square) -> Piece {
        self.board[s.0 as usize]
    }

    pub fn moved_piece(&self, m: Move) -> Piece {
        self.board[m.from().0 as usize]
    }

    pub fn pieces(&self) -> Bitboard {
        self.by_type_bb[ALL_PIECES.0 as usize]
    }

    pub fn pieces_p(&self, pt: PieceType) -> Bitboard {
        self.by_type_bb[pt.0 as usize]
    }

    pub fn pieces_pp(&self, pt1: PieceType, pt2: PieceType) -> Bitboard {
        self.pieces_p(pt1) | self.pieces_p(pt2)
    }

    pub fn pieces_c(&self, c: Color) -> Bitboard {
        self.by_color_bb[c.0 as usize]
    }

    pub fn pieces_cp(&self, c: Color, pt: PieceType) -> Bitboard {
        self.pieces_c(c) & self.pieces_p(pt)
    }

    pub fn pieces_cpp(
        &self, c: Color, pt1: PieceType, pt2: PieceType,
    ) -> Bitboard {
        self.pieces_c(c) & self.pieces_pp(pt1, pt2)
    }

    pub fn count(&self, c: Color, pt: PieceType) -> i32 {
        self.piece_count[Piece::make(c, pt).0 as usize]
    }

    pub fn squares(&self, c: Color, pt: PieceType) -> &[Square] {
        &self.piece_list[Piece::make(c, pt).0 as usize]
    }

    pub fn square_list(&self, c: Color, pt: PieceType) -> SquareList {
        SquareList::construct(self.squares(c, pt))
    }

    pub fn square(&self, c: Color, pt: PieceType) -> Square {
        self.squares(c, pt)[0]
    }

    pub fn ep_square(&self) -> Square {
        self.st().ep_square
    }

    pub fn has_castling_right(&self, cr: CastlingRight) -> bool {
        self.st().castling_rights & cr != 0
    }

    pub fn castling_rights(&self, c: Color) -> CastlingRight {
        self.st().castling_rights & CastlingRight(3 << (2 * c.0))
    }

    pub fn can_castle(&self, c: Color) -> bool {
        self.castling_rights(c) != 0
    }

    pub fn castling_impeded(&self, cr: CastlingRight) -> bool {
        self.pieces() & self.castling_path[cr.0 as usize] != Bitboard(0)
    }

    pub fn castling_rook_square(&self, cr: CastlingRight) -> Square {
        self.castling_rook_square[cr.0 as usize]
    }

    pub fn attacks_from_pawn(&self, s: Square, c: Color) -> Bitboard {
        pawn_attacks(c, s)
    }

    pub fn attacks_from(&self, pt: PieceType, s: Square) -> Bitboard {
        debug_assert!(pt != PAWN);
        match pt {
            BISHOP | ROOK => attacks_bb(pt, s, self.pieces()),
            QUEEN => self.attacks_from(ROOK, s) | self.attacks_from(BISHOP, s),
            _ => pseudo_attacks(pt, s)
        }
    }

    pub fn attackers_to_occ(&self, s: Square, occ: Bitboard) -> Bitboard {
          (self.attacks_from_pawn(s, BLACK) & self.pieces_cp(WHITE, PAWN))
        | (self.attacks_from_pawn(s, WHITE) & self.pieces_cp(BLACK, PAWN))
        | (self.attacks_from(KNIGHT, s)     & self.pieces_p(KNIGHT))
        | (     attacks_bb(ROOK, s, occ)    & self.pieces_pp(ROOK, QUEEN))
        | (     attacks_bb(BISHOP, s, occ)  & self.pieces_pp(BISHOP, QUEEN))
        | (self.attacks_from(KING, s)       & self.pieces_p(KING))
    }

    pub fn attackers_to(&self, s: Square) -> Bitboard {
        self.attackers_to_occ(s, self.by_type_bb[ALL_PIECES.0 as usize])
    }

    pub fn checkers(&self) -> Bitboard {
        self.st().checkers_bb
    }

    pub fn blockers_for_king(&self, c: Color) -> Bitboard {
        self.st().blockers_for_king[c.0 as usize]
    }

    pub fn pinners_for_king(&self, c: Color) -> Bitboard {
        self.st().pinners_for_king[c.0 as usize]
    }

    pub fn discovered_check_candidates(&self) -> Bitboard {
        self.blockers_for_king(!self.side_to_move)
        & self.pieces_c(self.side_to_move)
    }

    pub fn pinned_pieces(&self, c: Color) -> Bitboard {
        self.blockers_for_king(c) & self.pieces_c(c)
    }

    pub fn check_squares(&self, pt: PieceType) -> Bitboard {
        self.st().check_squares[pt.0 as usize]
    }

    pub fn pawn_passed(&self, c: Color, s: Square) -> bool {
        self.pieces_cp(!c, PAWN) & passed_pawn_mask(c, s) == 0
    }

    pub fn advanced_pawn_push(&self, m: Move) -> bool {
        self.moved_piece(m).piece_type() == PAWN
        && m.from().relative_rank(self.side_to_move()) > RANK_4
    }

    pub fn key(&self) -> Key {
        self.st().key
    }

    pub fn pawn_key(&self) -> Key {
        self.st().pawn_key
    }

    pub fn material_key(&self) -> Key {
        self.st().material_key
    }

    pub fn psq_score(&self) -> Score {
        self.st().psq
    }

    pub fn non_pawn_material_c(&self, c: Color) -> Value {
        self.st().non_pawn_material[c.0 as usize]
    }

    pub fn non_pawn_material(&self) -> Value {
        self.non_pawn_material_c(WHITE) + self.non_pawn_material_c(BLACK)
    }

    pub fn game_ply(&self) -> i32 {
        self.game_ply
    }

    pub fn rule50_count(&self) -> i32 {
        self.st().rule50
    }

    pub fn opposite_bishops(&self) -> bool {
        self.piece_count[W_BISHOP.0 as usize] == 1
        && self.piece_count[B_BISHOP.0 as usize] == 1
        && opposite_colors( self.square(WHITE, BISHOP),
            self.square(BLACK, BISHOP))
    }

    pub fn is_chess960(&self) -> bool {
        self.chess960
    }

    pub fn capture_or_promotion(&self, m: Move) -> bool {
        debug_assert!(m.is_ok());
        if m.move_type() != NORMAL {
            m.move_type() != CASTLING
        } else {
            !self.empty(m.to())
        }
    }

    pub fn capture(&self, m: Move) -> bool {
        debug_assert!(m.is_ok());
        (!self.empty(m.to()) && m.move_type() != CASTLING)
        || m.move_type() == ENPASSANT
    }

    pub fn captured_piece(&self) -> Piece {
        self.st().captured_piece
    }

    pub const PIECE_TO_CHAR: &'static str = " PNBRQK  pnbrqk";

    pub fn print(&mut self) {
        println!("\n +---+---+---+---+---+---+---+---+");
        for r in (0..8).rev() {
            for f in 0..8 {
                print!(" | {}", Position::PIECE_TO_CHAR
                        .chars()
                        .nth(self.piece_on(Square::make(f, r)).0 as usize)
                        .unwrap());
            }
            println!(" |\n +---+---+---+---+---+---+---+---+");
        }

        println!("\nFen: {}\nKey: {}\nCheckers: {}", self.fen(), self.key(),
            self.checkers());

        if tb::max_cardinality() >= popcount(self.pieces())
            && !self.has_castling_right(ANY_CASTLING)
        {
            let mut s1 = 1;
            let mut s2 = 1;
            let wdl = tb::probe_wdl(self, &mut s1);
            let dtz = tb::probe_dtz(self, &mut s2);
            println!("Tablebases WDL: {} ({})\nTablebases DTZ: {} ({})",
                wdl, s1, dtz, s2);
            if s1 != 0 {
                let dtm = tb::probe_dtm(self, wdl, &mut s1);
                println!("Tablebases DTM: {} ({})", uci::value(dtm), s1);
            }
        }
    }

    // set() initializes the position objection with the given FEN string.
    // This function is not very robust - make sure that input FENs are
    // correct. This is assumed to be the responsibility of the GUI.
 
    pub fn set(&mut self, fen_str: &str, is_chess960: bool) {
        for c in 0..2 {
            self.by_color_bb[c] = Bitboard(0);
        }
        for t in 0..8 {
            self.by_type_bb[t] = Bitboard(0);
        }
        for i in 0..16 {
            self.piece_count[i] = 0;
            self.castling_path[i] = Bitboard(0);
            self.castling_rook_square[i] = Square::NONE;
            for j in 0..16 {
                self.piece_list[i][j] = Square::NONE;
            }
        }
        for i in 0..64 {
            self.board[i] = NO_PIECE;
            self.castling_rights_mask[i] = CastlingRight(0);
        }

        let mut iter = fen_str.split_whitespace();

        // 1. Piece placement
        let pieces = iter.next().unwrap();
        let mut sq = Square::A8;
        for c in pieces.chars() {
            if let Some(d) = c.to_digit(10) {
                sq += (d as i32) * EAST; // Advance the given number of files
            } else if c == '/' {
                sq += 2 * SOUTH;
            } else if let Some(idx) = Position::PIECE_TO_CHAR.find(c) {
                self.put_piece(Piece(idx as u32), sq);
                sq += EAST;
            }
        }

        // 2. Active color
        let color = iter.next().unwrap();
        self.side_to_move = if color == "b" { BLACK } else { WHITE };

        // 3. Castling availability. Compatible with 3 standards: Normal FEN
        // standard, Shredder-FEN that uses the letters of the columns on
        // which the rooks began the game instead of KQkq and also X-FEN
        // standard that, in case of Chess960, if an inner rook is associated
        // with the castling right, the castling tag is replaced by the file
        // letter of the involved rook, as for the Shredder-FEN.
        let castling = iter.next().unwrap();
        if castling != "-" {
            for c in castling.chars() {
                let color = if c.is_lowercase() { BLACK } else { WHITE };
                let rook = Piece::make(color, ROOK);
                let side = c.to_uppercase().next().unwrap();
                let mut rsq;
                if side == 'K' {
                    rsq = Square::H1.relative(color);
                    while self.piece_on(rsq) != rook {
                        rsq += WEST;
                    }
                } else if side == 'Q' {
                    rsq = Square::A1.relative(color);
                    while self.piece_on(rsq) != rook {
                        rsq += EAST;
                    }
                } else if side >= 'A' && side <= 'H' {
                    let file = side.to_digit(18).unwrap() - 10;
                    rsq = Square::make(file, relative_rank(color, RANK_1));
                } else {
                    continue;
                }
                self.set_castling_right(color, rsq);
            }
        }

        // 4. En passant square. Ignore if no pawn capture is possible
        let enpassant = iter.next().unwrap();
        self.st_mut().ep_square = Square::NONE;
        if enpassant != "-" {
            let file = enpassant.chars().nth(0).unwrap();
            let file = file.to_digit(18).unwrap() - 10;
            let rank = if self.side_to_move == WHITE { 5 } else { 2 };
            let ep_sq = Square::make(file, rank);
            if self.attackers_to(ep_sq)
                    & self.pieces_cp(self.side_to_move, PAWN) != 0
                && self.pieces_cp(!self.side_to_move, PAWN)
                    & (ep_sq + pawn_push(!self.side_to_move)) != 0
            {
                self.st_mut().ep_square = ep_sq;
            }
        }

        // 5-6. Halfmvoe clock and fullmove number
        if let Some(halfmove) = iter.next() {
            self.st_mut().rule50 = halfmove.parse::<i32>().unwrap();
        } else {
            self.st_mut().rule50 = 0;
        }

        // Convert from fullmove starting from 1 to game_ply starting from 0.
        // Handle also common incorrect FEN with fullmove = 0.
        if let Some(fullmove) = iter.next() {
            let fullmove = fullmove.parse::<i32>().unwrap();
            self.game_ply = std::cmp::max(2 * (fullmove - 1), 0);
        } else {
            self.game_ply = 0;
        }
        if self.side_to_move == BLACK {
            self.game_ply += 1;
        }

        self.chess960 = is_chess960;
        self.set_state();

        debug_assert!(self.is_ok());
    }

    // set_castling_right() is a helper function used to set castling rights
    // given the corresponding color and the rook starting square.

    fn set_castling_right(&mut self, c: Color, rfrom: Square) {
        let kfrom = self.square(c, KING);
        let cs = if kfrom < rfrom { CastlingSide::KING }
            else { CastlingSide::QUEEN };
        let cr = c | cs;

        self.st_mut().castling_rights |= cr;
        self.castling_rights_mask[kfrom.0 as usize] |= cr;
        self.castling_rights_mask[rfrom.0 as usize] |= cr;
        self.castling_rook_square[cr.0 as usize] = rfrom;

        let kto = relative_square(c, if cs == CastlingSide::KING { Square::G1 } else { Square::C1 });
        let rto = relative_square(c, if cs == CastlingSide::KING { Square::F1 } else { Square::D1 });

        let mut s = std::cmp::min(rfrom, rto);
        while s <= std::cmp::max(rfrom, rto) {
            if s != kfrom && s != rfrom {
                self.castling_path[cr.0 as usize] |= s;
            }
            s += EAST;
        }

        let mut s = std::cmp::min(kfrom, kto);
        while s <= std::cmp::max(kfrom, kto) {
            if s != kfrom && s != rfrom {
                self.castling_path[cr.0 as usize] |= s;
            }
            s += EAST;
        }
    }

    // set_check_info() sets king attacks to detect if a move gives cehck

    fn set_check_info(&mut self) {
        let mut pinners = Bitboard(0);
        self.st_mut().blockers_for_king[WHITE.0 as usize] =
            self.slider_blockers(self.pieces_c(BLACK),
                self.square(WHITE, KING), &mut pinners);
        self.st_mut().pinners_for_king[WHITE.0 as usize] = pinners;
        self.st_mut().blockers_for_king[BLACK.0 as usize] =
            self.slider_blockers(self.pieces_c(WHITE),
                self.square(BLACK, KING), &mut pinners);
        self.st_mut().pinners_for_king[BLACK.0 as usize] = pinners;

        let ksq = self.square(!self.side_to_move(), KING);

        self.st_mut().check_squares[PAWN.0 as usize] =
            self.attacks_from_pawn(ksq, !self.side_to_move);
        self.st_mut().check_squares[KNIGHT.0 as usize] =
            self.attacks_from(KNIGHT, ksq);
        self.st_mut().check_squares[BISHOP.0 as usize] =
        self.attacks_from(BISHOP, ksq);
        self.st_mut().check_squares[ROOK.0 as usize] =
            self.attacks_from(ROOK, ksq);
        self.st_mut().check_squares[QUEEN.0 as usize] =
            self.st().check_squares[BISHOP.0 as usize]
            | self.st().check_squares[ROOK.0 as usize];
        self.st_mut().check_squares[KING.0 as usize] = Bitboard(0);
    }

    // set_state() computes the hash keys of the position, and other data
    // that once computed is updated incrementally as moves are made.
    // The function is used only when a new position is set up, and to verify
    // the correctness of the StateInfo data when running in debug mode.

    fn set_state(&mut self) {
        self.st_mut().key = Key(0);
        self.st_mut().material_key = Key(0);
        self.st_mut().pawn_key = zobrist::no_pawns();
        self.st_mut().non_pawn_material[WHITE.0 as usize] = Value::ZERO;
        self.st_mut().non_pawn_material[BLACK.0 as usize] = Value::ZERO;
        self.st_mut().psq = Score::ZERO;
        self.st_mut().checkers_bb =
            self.attackers_to(self.square(self.side_to_move, KING))
            & self.pieces_c(!self.side_to_move);

        self.set_check_info();

        for s in self.pieces() {
            let pc = self.piece_on(s);
            self.st_mut().key ^= zobrist::psq(pc, s);
            self.st_mut().psq += psqt::psq(pc, s);
        }

        if self.st_mut().ep_square != Square::NONE {
            self.st_mut().key ^=
                zobrist::enpassant(self.st().ep_square.file());
        }

        if self.side_to_move == BLACK {
            self.st_mut().key ^= zobrist::side();
        }

        self.st_mut().key ^= zobrist::castling(self.st().castling_rights);

        for s in self.pieces_p(PAWN) {
            self.st_mut().pawn_key ^= zobrist::psq(self.piece_on(s), s);
        }

        for c in 0..2 {
            for pt in 2..6 {
                let pc = Piece::make(Color(c), PieceType(pt));
                self.st_mut().non_pawn_material[c as usize] +=
                    self.count(Color(c), PieceType(pt)) * piece_value(MG, pc);
            }

            for pt in 1..7 {
                let pc = Piece::make(Color(c), PieceType(pt));
                for cnt in 0..self.count(Color(c), PieceType(pt)) {
                    self.st_mut().material_key ^= zobrist::material(pc, cnt);
                }
            }
        }
    }

    // fen() returns a FEN representation of the position. In case of Chess960
    // the Shredder-FEN notation is used.

    pub fn fen(&self) -> String {
        let mut ss = String::new();

        for r in (0..8).rev() {
            let mut f = 0;
            while f < 8 {
                let mut empty_cnt = 0u8;
                while f < 8 && self.empty(Square::make(f, r)) {
                    empty_cnt += 1;
                    f += 1;
                }
                if empty_cnt > 0 {
                    ss.push((48u8 + empty_cnt) as char);
                }
                if f < 8 {
                    let c = Position::PIECE_TO_CHAR.chars()
                        .nth(self.piece_on(Square::make(f, r)).0 as usize)
                        .unwrap();
                    ss.push(c);
                    f += 1;
                }
            }
            if r > 0 {
                ss.push('/');
            }
        }

        ss.push_str(if self.side_to_move == WHITE { " w " } else { " b " });

        self.castle_helper(&mut ss, WHITE_OO, 'K');
        self.castle_helper(&mut ss, WHITE_OOO, 'Q');
        self.castle_helper(&mut ss, BLACK_OO, 'k');
        self.castle_helper(&mut ss, BLACK_OOO, 'q');

        if !self.has_castling_right(ANY_CASTLING) {
            ss.push('-');
        }

        if self.ep_square() == Square::NONE {
            ss.push_str(" - ");
        } else {
            ss.push(' ');
            ss.push_str(&uci::square(self.ep_square()));
            ss.push(' ');
        }

        ss.push_str(&self.rule50_count().to_string());
        ss.push(' ');
        ss.push_str(&(1 + self.game_ply() / 2).to_string());

        ss
    }

    fn castle_helper(&self, ss: &mut String, cr: CastlingRight, c: char) {
        if !self.has_castling_right(cr) {
            return;
        }

        if !self.chess960 {
            ss.push(c);
        } else {
            let f = self.castling_rook_square(cr).file();
            let r = self.castling_rook_square(cr).rank();
            let mut c = 65 + f;
            if r == RANK_8 {
                c += 32;
            }
            ss.push((c as u8) as char);
        }
    }

    // slider_blockers() returns a bitboard of all the pieces (both colors)
    // that are blocking attacks on the square 's' from 'sliders'. A piece
    // blocks a slider if removing that piece from the board would result
    // in a position where square 's'is attacked. For example, a king attack
    // blocking piece can be either a pinned or a discovered check piece,
    // depending on whether its color is the opposite of or the same as the
    // color of the slider.

    pub fn slider_blockers(
        &self,
        sliders: Bitboard,
        s: Square,
        pinners: &mut Bitboard
    ) -> Bitboard {
        let mut result = Bitboard(0);
        *pinners = Bitboard(0);

        // Snipers are sliders that attack 's' when a piece is removed
        let snipers =
            ((pseudo_attacks(ROOK, s) & self.pieces_pp(QUEEN, ROOK))
                | (pseudo_attacks(BISHOP, s) & self.pieces_pp(QUEEN, BISHOP)))
            & sliders;

        for sniper_sq in snipers {
            let b = between_bb(s, sniper_sq) & self.pieces();

            if !more_than_one(b) {
                result |= b;
                if b & self.pieces_c(self.piece_on(s).color()) != 0 {
                    *pinners |= sniper_sq;
                }
            }
        }
        result
    }

    // legal() tests whether a pseudo-legal move is legal

    pub fn legal(&self, m: Move) -> bool {
        debug_assert!(m.is_ok());

        let us = self.side_to_move;
        let from = m.from();

        debug_assert!(self.moved_piece(m).color() == us);
        debug_assert!(
            self.piece_on(self.square(us, KING)) == Piece::make(us, KING)
        );

        // En passant captures are a tricky special case. Because they are
        // uncommon, we do it simply by testing whether the king is attacked
        // after the move is made.
        if m.move_type() == ENPASSANT {
            let ksq = self.square(us, KING);
            let to = m.to();
            let capsq = to - pawn_push(us);
            let occupied = (self.pieces() ^ from ^ capsq) | to;

            debug_assert!(to == self.ep_square());
            debug_assert!(self.moved_piece(m) == Piece::make(us, PAWN));
            debug_assert!(self.piece_on(capsq) == Piece::make(!us, PAWN));
            debug_assert!(self.piece_on(to) == NO_PIECE);

            return
                attacks_bb(ROOK, ksq, occupied)
                    & self.pieces_cpp(!us, QUEEN, ROOK) == 0
                && attacks_bb(BISHOP, ksq, occupied)
                    & self.pieces_cpp(!us, QUEEN, BISHOP) == 0;
        }

        // If the moving piece is a king, check whether the destination
        // square is attacked by the opponent. Castling moves are checked
        // for legality during move generation.
        if self.piece_on(from).piece_type() == KING {
            return m.move_type() == CASTLING
                || self.attackers_to(m.to()) & self.pieces_c(!us) == 0;
        }

        // A non-king move is legal if and only if it is not pinned or it
        // is moving along the ray towards or away from the king.
        self.pinned_pieces(us) & from == 0
        || aligned(from, m.to(), self.square(us, KING))
    }

    // pseudo_legal() takes a random move and tests whether the move is
    // pseudo legal. It is used to validate moves from T that can be
    // corrupted due to SMP concurrent access or hash position key aliasing.

    pub fn pseudo_legal(&self, m: Move) -> bool {
        let us = self.side_to_move();
        let from = m.from();
        let to = m.to();
        let pc = self.moved_piece(m);

        // Use a slower but simpler function for uncommon cases
        if m.move_type() != NORMAL {
            return MoveList::new::<Legal>(self).contains(m);
        }

        // It is not a promotion, so promotion piece must be empty
        if m.promotion_type() != KNIGHT {
            return false;
        }

        // If the 'from' square is not occupied by a piece belonging to the
        // side to move, the move is obviously not legal.
        if pc == NO_PIECE || pc.color() != us {
            return false;
        }

        // The destination square cannot be occupied by a friendly piece
        if self.pieces_c(us) & to != 0 {
            return false;
        }

        // Handle the special case of a pawn move
        if pc.piece_type() == PAWN {
            // We have already handled promotion moves, so destination
            // cannot be on the 8th/1st rank.
            if to.rank() == relative_rank(us, RANK_8) {
                return false;
            }

            if self.attacks_from_pawn(from, us) & self.pieces_c(!us) & to == 0
                && !((from + pawn_push(us) == to) && self.empty(to))
                && !(  from + 2 * pawn_push(us) == to
                    && from.rank() == relative_rank(us, RANK_2)
                    && self.empty(to)
                    && self.empty(to - pawn_push(us)))
            {
                return false;
            }
        } else if self.attacks_from(pc.piece_type(), from) & to == 0 {
            return false;
        }

        // Evasions generator already takes care of avoiding certain kinds of
        // illegal moves and legal() relies on this. We therefore have to take
        // care that the same kind of moves are filtered out here.
        if self.checkers() != 0 {
            if pc.piece_type() != KING {
                // Double check? In this case a king move is required
                if more_than_one(self.checkers()) {
                    return false;
                }

                // Our move must be a blocking evasion or a capture of the
                // checking piece
                if (between_bb(lsb(self.checkers()), self.square(us, KING))
                        | self.checkers())
                    & to == 0
                {
                    return false;
                }
            }
            // In case of king moves under check we have to remove king so as
            // to catch invalid moves like b1a1 when opposite queen is on c1.
            else if self.attackers_to_occ(to, self.pieces() ^ from)
                    & self.pieces_c(!us) != 0
            {
                return false;
            }
        }

        true
    }

    // gives_check() tests whether a pseudo-legal move gives a check

    pub fn gives_check(&self, m: Move) -> bool {
        debug_assert!(m.is_ok());
        debug_assert!(self.moved_piece(m).color() == self.side_to_move());

        let from = m.from();
        let to = m.to();

        // Is there a direct check?
        if self.st().check_squares[self.piece_on(from).piece_type().0 as usize]
            & to != 0
        {
            return true;
        }

        // Is there a discovered check?
        if self.discovered_check_candidates() & from != 0
            && !aligned(from, to, self.square(!self.side_to_move(), KING))
        {
            return true;
        }

        match m.move_type() {

            NORMAL => false,

            PROMOTION => {
                attacks_bb(m.promotion_type(), to, self.pieces() ^ from)
                & self.square(!self.side_to_move(), KING) != 0
            }

            // En passant capture with check? We have already handled the
            // case of direct checks and ordinary discovered check, so the
            // only case we need to handle is the unusual case of a
            // discovered check through the captured pawn.
            ENPASSANT => {
                let capsq = Square::make(to.file(), from.rank());
                let b = (self.pieces() ^ from ^ capsq) | to;

                (attacks_bb(ROOK, self.square(!self.side_to_move(), KING), b)
                    & self.pieces_cpp(self.side_to_move(), QUEEN, ROOK))
                | (attacks_bb(BISHOP,
                              self.square(!self.side_to_move(), KING),
                              b)
                    & self.pieces_cpp(self.side_to_move(), QUEEN, BISHOP)) != 0
            }

            CASTLING => {
                let kfrom = from;
                let rfrom = to; // Castling is encoded as king captures rook
                let kto = relative_square(
                    self.side_to_move(),
                    if rfrom > kfrom { Square::G1 } else { Square::C1 }
                );
                let rto = relative_square(
                    self.side_to_move(),
                    if rfrom > kfrom { Square::F1 } else { Square::D1 }
                );

                (pseudo_attacks(ROOK, rto)
                    & self.square(!self.side_to_move(), KING)) != 0
                && (attacks_bb(ROOK, rto,
                        (self.pieces() ^ kfrom ^ rfrom) | rto | kto)
                    & self.square(!self.side_to_move(), KING)) != 0
            }

            _ => {
                debug_assert!(false);
                false
            }
        }
    }

    // do_move() makes a move and saves all information necessary to a
    // StateInfo object. The move is assumed to be legal. Pseudo-legal
    // moves should be filtered out before this function is called.

    pub fn do_move(&mut self, m: Move, gives_check: bool) {
        debug_assert!(m.is_ok());

        self.nodes += 1;
        let mut k = self.st().key ^ zobrist::side();

        // Copy some fields of the old state to our new StateInfo object
        // except the ones which are going to be recalculated from scratch
        // anyway.
        let st_copy = self.st().copy();
        self.states.push(st_copy);

        // Increment ply counters. The rule50 field will be reset to zero
        // later on in case of a capture or a pawn move.
        self.game_ply += 1;
        self.st_mut().rule50 += 1;
        self.st_mut().plies_from_null += 1;

        let us = self.side_to_move();
        let them = !us;
        let from = m.from();
        let mut to = m.to();
        let pc = self.piece_on(from);
        let mut captured =
            if m.move_type() == ENPASSANT {
                Piece::make(them, PAWN)
            } else {
                self.piece_on(to)
            };

        debug_assert!(pc.color() == us);
        debug_assert!(
            captured == NO_PIECE
            || captured.color() ==
                if m.move_type() != CASTLING { them } else { us }
        );

        if m.move_type() == CASTLING {
            debug_assert!(pc == Piece::make(us, KING));
            debug_assert!(captured == Piece::make(us, ROOK));

            let mut rfrom = Square::A1;
            let mut rto = Square::A1;
            self.do_castling::<True>(us, from, &mut to, &mut rfrom, &mut rto);

            self.st_mut().psq +=
                psqt::psq(captured, rto) - psqt::psq(captured, rfrom);
            k ^= zobrist::psq(captured, rfrom) ^ zobrist::psq(captured, rto);
            captured = NO_PIECE;
        }

        if captured != NO_PIECE {
            let mut capsq = to;

            // If the captured piece is a pawn, update pawn hash key, otherwise
            // update non-pawn material.
            if captured.piece_type() == PAWN {
                if m.move_type() == ENPASSANT {
                    capsq -= pawn_push(us);

                    debug_assert!(pc == Piece::make(us, PAWN));
                    debug_assert!(to == self.st_mut().ep_square);
                    debug_assert!(to.relative_rank(us) == RANK_6);
                    debug_assert!(self.piece_on(to) == NO_PIECE);
                    debug_assert!(
                        self.piece_on(capsq) == Piece::make(them, PAWN)
                    );

                    self.board[capsq.0 as usize] = NO_PIECE;
                }

                self.st_mut().pawn_key ^= zobrist::psq(captured, capsq);
            } else {
                self.st_mut().non_pawn_material[them.0 as usize] -=
                    piece_value(MG, captured);
            }

            // Update board and piece lists
            self.remove_piece(captured, capsq);

            // Update material hash key and prefetch access to material_table
            k ^= zobrist::psq(captured, capsq);
            self.st_mut().material_key ^= zobrist::material(captured,
                self.piece_count[captured.0 as usize]);
            // prefetch

            // Update incremental scores
            self.st_mut().psq -= psqt::psq(captured, capsq);

            // Reset rule 50 counter
            self.st_mut().rule50 = 0;
        }

        // Update hash key
        k ^= zobrist::psq(pc, from) ^ zobrist::psq(pc, to);

        // Reset en passant square
        if self.st_mut().ep_square != Square::NONE {
            k ^= zobrist::enpassant(self.st().ep_square.file());
            self.st_mut().ep_square = Square::NONE;
        }

        // Update castling rights if needed
        if self.st_mut().castling_rights != 0
            && self.castling_rights_mask[from.0 as usize]
                | self.castling_rights_mask[to.0 as usize] != 0
        {
            let cr =
                self.castling_rights_mask[from.0 as usize]
                | self.castling_rights_mask[to.0 as usize];
            k ^= zobrist::castling(self.st().castling_rights & cr);
            self.st_mut().castling_rights &= !cr;
        }

        // Move the piece. The tricky Chess960 castling is handled earlier
        if m.move_type() != CASTLING {
            self.move_piece(pc, from, to);
        }

        // If the moving piece is a pawn do some special extra work
        if pc.piece_type() == PAWN {
            // Set en-passant square if the moved pawn can be captured
            if to.0 ^ from.0 == 16
                && self.attacks_from_pawn(to - pawn_push(us), us)
                    & self.pieces_cp(them, PAWN) != 0
            {
                self.st_mut().ep_square = to - pawn_push(us);
                k ^= zobrist::enpassant(self.st().ep_square.file());
            } else if m.move_type() == PROMOTION {
                let promotion = Piece::make(us, m.promotion_type());

                debug_assert!(to.relative_rank(us) == RANK_8);
                debug_assert!(
                    promotion.piece_type() >= KNIGHT
                    && promotion.piece_type() <= QUEEN
                );

                self.remove_piece(pc, to);
                self.put_piece(promotion, to);

                // Update hash keys
                k ^= zobrist::psq(pc, to) ^ zobrist::psq(promotion, to);
                self.st_mut().pawn_key ^= zobrist::psq(pc, to);
                self.st_mut().material_key ^=
                    zobrist::material(promotion,
                        self.piece_count[promotion.0 as usize] - 1)
                    ^ zobrist::material(pc,
                        self.piece_count[pc.0 as usize]);

                // Update incremental score
                self.st_mut().psq +=
                    psqt::psq(promotion, to) - psqt::psq(pc, to);

                // Update material
                self.st_mut().non_pawn_material[us.0 as usize] +=
                    piece_value(MG, promotion);
            }

            // Update pawn hash key and prefetch access to pawns_table
            self.st_mut().pawn_key ^=
                zobrist::psq(pc, from) ^ zobrist::psq(pc, to);
            // prefetch2(...);

            // Reset rule 50 draw counter
            self.st_mut().rule50 = 0;
        }

        // Update incremental scores
        self.st_mut().psq += psqt::psq(pc, to) - psqt::psq(pc, from);

        // Set captured piece
        self.st_mut().captured_piece = captured;

        // Update the key with the final value
        self.st_mut().key = k;

        // Calculate checkers bitboard (if move gives check)
        self.st_mut().checkers_bb =
            if gives_check {
                self.attackers_to(self.square(them, KING)) & self.pieces_c(us)
            } else {
                Bitboard(0)
            };

        self.side_to_move = them;

        // Update king attacks used for fast check detection
        self.set_check_info();

        debug_assert!(self.is_ok());
    }

    // undo_move() unmakes a move. When it returns, the position should be
    // restored to exactly the same state as before the move was made.

    pub fn undo_move(&mut self, m: Move) {
        debug_assert!(m.is_ok());

        self.side_to_move = !self.side_to_move;

        let us = self.side_to_move;
        let from = m.from();
        let mut to = m.to();
        let mut pc = self.piece_on(to);

        debug_assert!(self.empty(from) || m.move_type() == CASTLING);
        debug_assert!(self.st().captured_piece.piece_type() != KING);

        if m.move_type() == PROMOTION {
            debug_assert!(to.relative_rank(us) == RANK_8);
            debug_assert!(pc.piece_type() == m.promotion_type());
            debug_assert!(
                pc.piece_type() >= KNIGHT && pc.piece_type() <= QUEEN
            );

            self.remove_piece(pc, to);
            pc = Piece::make(us, PAWN);
            self.put_piece(pc, to);
        }

        if m.move_type() == CASTLING {
            let mut rfrom = Square(0);
            let mut rto = Square(0);
            self.do_castling::<False>(us, from, &mut to, &mut rfrom, &mut rto);
        } else {
            // Put the piece back at the source square
            self.move_piece(pc, to, from);

            if self.st().captured_piece != NO_PIECE {
                let mut capsq = to;

                if m.move_type() == ENPASSANT {
                    capsq -= pawn_push(us);

                    debug_assert!(pc.piece_type() == PAWN);
                    debug_assert!(to.relative_rank(us) == RANK_6);
                    debug_assert!(self.piece_on(capsq) == NO_PIECE);
                    debug_assert!(
                        self.st().captured_piece == Piece::make(!us, PAWN)
                    );
                }

                // Restore the captured piece
                let cap_piece = self.st().captured_piece;
                self.put_piece(cap_piece, capsq);
            }
        }

        let new_len = self.states.len() - 1;
        self.states.truncate(new_len);
        self.game_ply -= 1;

        debug_assert!(self.is_ok());
    }

    // do_castling() is a helper used to do/undo a castling move. This is
    // a bit tricky in Chess960 where from/to squares can overlap.
    fn do_castling<Do: Bool>(
        &mut self, us: Color, from: Square, to: &mut Square,
        rfrom: &mut Square, rto: &mut Square,
    ) {
        let do_castle = Do::bool();
        let king_side = *to > from;
        *rfrom = *to; // Castling is encoded as king captures rook
        *rto = relative_square(
            us,
            if king_side { Square::F1 } else { Square::D1 }
        );
        *to = relative_square(
            us,
            if king_side { Square::G1 } else { Square::C1 }
        );

        // Remove both pieces first since squares could overlap in Chess960
        self.remove_piece(Piece::make(us, KING),
            if do_castle { from } else { *to });
        self.remove_piece(Piece::make(us, ROOK),
            if do_castle { *rfrom } else { *rto });
        self.board[(if do_castle { from } else { *to }).0 as usize] = NO_PIECE;
        self.board[(if do_castle { *rfrom } else { *rto }).0 as usize] =
            NO_PIECE;
        self.put_piece(Piece::make(us, KING),
            if do_castle { *to } else { from });
        self.put_piece(Piece::make(us, ROOK),
            if do_castle { *rto } else { *rfrom });
    }

    // do(undo)_null_move() is used to do(undo) a "null move": it flips the
    // side to move without executing any move on the board.

    pub fn do_null_move(&mut self) {
        debug_assert!(self.checkers() == 0);

        let st_copy = (*self.st()).clone(); // full copy
        self.states.push(st_copy);

        if self.st().ep_square != Square::NONE {
            self.st_mut().key ^=
                zobrist::enpassant(self.st().ep_square.file());
            self.st_mut().ep_square = Square::NONE;
        }

        self.st_mut().key ^= zobrist::side();
        // prefetch

        self.st_mut().rule50 += 1;
        self.st_mut().plies_from_null = 0;

        self.side_to_move = !self.side_to_move;

        self.set_check_info();

        debug_assert!(self.is_ok());
    }

    pub fn undo_null_move(&mut self) {
        debug_assert!(self.checkers() == 0);

        let new_len = self.states.len() - 1;
        self.states.truncate(new_len);
        self.side_to_move = !self.side_to_move;
    }

    // key_after() computes the new hash key after the given move. Needed
    // for specualtive prefetch. It does not recognize special moves like
    // castling, en-passant and promotions.

#[allow(dead_code)]
    fn key_after(&self, m: Move) -> Key {
        let from = m.from();
        let to = m.to();
        let pc = self.piece_on(from);
        let captured = self.piece_on(to);
        let mut k = self.st().key ^ zobrist::side();

        if captured != NO_PIECE {
            k ^= zobrist::psq(captured, to);
        }

        k ^ zobrist::psq(pc, to) ^ zobrist::psq(pc, from)
    }

    // see_ge() tests if the SEE value of move is greater than or equal to
    // the given threshold. We use an algorithm similar to alpha-beta pruning
    // with a null window.

    pub fn see_ge(&self, m: Move, value: Value) -> bool {
        debug_assert!(m.is_ok());

        // Only deal with normal moves, assume others pass a simple see
        if m.move_type() != NORMAL {
            return Value::ZERO >= value;
        }

        let from = m.from();
        let to = m.to();

        // The opponent may be able to recapture so this is the best result
        // we can hope for.
        let mut swap = piece_value(MG, self.piece_on(to)) - value;
        if swap < Value::ZERO {
            return false;
        }

        // Now assume the worst possible result: that the opponent can
        // capture our piece for free.
        swap = piece_value(MG, self.piece_on(from)) - swap;
        if swap <= Value::ZERO {
            return true;
        }

        // Find all attackers to the destination square, with the moving piece
        // removed, but possibly an X-ray attacked added behind it.
        let mut occ = self.pieces() ^ from ^ to;
        let mut stm = self.piece_on(from).color();
        let mut attackers = self.attackers_to_occ(to, occ);
        let mut res = Value(1);

        loop {
            stm = !stm;
            attackers &= occ;
            let mut stm_attackers = attackers & self.pieces_c(stm);
            if stm_attackers == 0 {
                break;
            }
            if stm_attackers & self.blockers_for_king(stm) != 0
                && self.pinners_for_king(stm) & !occ == 0
            {
                stm_attackers &= !self.blockers_for_king(stm);
            }
            if stm_attackers == 0 {
                break;
            }
            res = Value(res.0 ^ 1);
            let bb = stm_attackers & self.pieces_p(PAWN);
            if bb != 0 {
                swap = PawnValueMg - swap;
                if swap < res {
                    break;
                }
                occ ^= bb & -bb;
                attackers |=
                    attacks_bb(BISHOP, to, occ) & self.pieces_pp(BISHOP, QUEEN);
                continue;
            }
            let bb = stm_attackers & self.pieces_p(KNIGHT);
            if bb != 0 {
                swap = KnightValueMg - swap;
                if swap < res {
                    break;
                }
                occ ^= bb & -bb;
                continue;
            }
            let bb = stm_attackers & self.pieces_p(BISHOP);
            if bb != 0 {
                swap = BishopValueMg - swap;
                if swap < res {
                    break;
                }
                occ ^= bb & -bb;
                attackers |=
                    attacks_bb(BISHOP, to, occ) & self.pieces_pp(BISHOP, QUEEN);
                continue;
            }
            let bb = stm_attackers & self.pieces_p(ROOK);
            if bb != 0 {
                swap = RookValueMg - swap;
                if swap < res {
                    break;
                }
                occ ^= bb & -bb;
                attackers |=
                    attacks_bb(ROOK, to, occ) & self.pieces_pp(ROOK, QUEEN);
                continue;
            }
            let bb = stm_attackers & self.pieces_p(QUEEN);
            if bb != 0 {
                swap = QueenValueMg - swap;
                if swap < res {
                    break;
                }
                occ ^= bb & -bb;
                attackers |=
                    (attacks_bb(BISHOP, to, occ)
                        & self.pieces_pp(BISHOP, QUEEN))
                    | (attacks_bb(ROOK, to, occ) & self.pieces_pp(ROOK, QUEEN));
                continue;
            }
            if attackers & !self.pieces_c(stm) != 0 {
                return res == Value::ZERO;
            } else {
                return res != Value::ZERO;
            }
        }
        res != Value::ZERO
    }

    // is_draw() tests whether the position is drawn by 50-move rule or by
    // repetition. It does not detect stalemates.

    pub fn is_draw(&self, ply: i32) -> bool {
        if self.st().rule50 > 99
            && (self.checkers() == 0
                || MoveList::new::<Legal>(&self).size() != 0)
        {
            return true;
        }

        let end = std::cmp::min(self.st().rule50, self.st().plies_from_null);

        if end < 4 {
            return false;
        }

        let mut k = self.states.len() - 3;
        let mut cnt = 0;

        let mut i = 4;
        while i <= end {
            k -= 2;

            // Return a draw score if a position repeats once earlier but
            // strictly after the root, or repeats twice before or at the
            // root.
            if self.states[k].key == self.st().key {
                cnt += 1;
                if cnt + ((ply > i) as i32) == 2 {
                    return true;
                }
            }

            i += 2;
        }

        false
    }

    pub fn has_repeated(&self) -> bool {
        let mut l = self.states.len() - 1;
        loop {
            let mut i = 4;
            let e = std::cmp::min(self.states[l].rule50,
                self.states[l].plies_from_null);

            if e < i {
                return false;
            }

            let mut k = self.states.len() - 3;

            while i <= e {
                k -= 2;

                if self.states[k].key == self.states[l].key {
                    return true;
                }

                i += 2;
            }

            l -= 2;
        }
    }

    fn put_piece(&mut self, pc: Piece, s: Square) {
        self.board[s.0 as usize] = pc;
        self.by_type_bb[ALL_PIECES.0 as usize] |= s;
        self.by_type_bb[pc.piece_type().0 as usize] |= s;
        self.by_color_bb[pc.color().0 as usize] |= s;
        self.index[s.0 as usize] = self.piece_count[pc.0 as usize];
        self.piece_count[pc.0 as usize] += 1;
        self.piece_list[pc.0 as usize][self.index[s.0 as usize] as usize] = s;
        self.piece_count[Piece::make(pc.color(), ALL_PIECES).0 as usize] += 1;
    }

    fn remove_piece(&mut self, pc: Piece, s: Square) {
        self.by_type_bb[ALL_PIECES.0 as usize] ^= s;
        self.by_type_bb[pc.piece_type().0 as usize] ^= s;
        self.by_color_bb[pc.color().0 as usize] ^= s;
        self.piece_count[pc.0 as usize] -= 1;
        let last_square = self.piece_list[pc.0 as usize]
            [self.piece_count[pc.0 as usize] as usize];
        self.index[last_square.0 as usize] = self.index[s.0 as usize];
        self.piece_list[pc.0 as usize]
            [self.index[last_square.0 as usize] as usize] = last_square;
        self.piece_list[pc.0 as usize]
            [self.piece_count[pc.0 as usize] as usize] = Square::NONE;
        self.piece_count[Piece::make(pc.color(), ALL_PIECES).0 as usize] -= 1;
    }

    fn move_piece(&mut self, pc: Piece, from: Square, to: Square) {
        let from_to_bb = from.bb() ^ to.bb();
        self.by_type_bb[ALL_PIECES.0 as usize] ^= from_to_bb;
        self.by_type_bb[pc.piece_type().0 as usize] ^= from_to_bb;
        self.by_color_bb[pc.color().0 as usize] ^= from_to_bb;
        self.board[from.0 as usize] = NO_PIECE;
        self.board[to.0 as usize] = pc;
        self.index[to.0 as usize] = self.index[from.0 as usize];
        self.piece_list[pc.0 as usize][self.index[to.0 as usize] as usize] =
            to;
    }

    // is_ok() performs some consistency checks for the position object and
    // raises an assert if something wrong is detected. This is meant to be
    // helpful when debugging.

    pub fn is_ok(&self) -> bool {
        if self.side_to_move() != WHITE && self.side_to_move != BLACK
            || self.piece_on(self.square(WHITE, KING)) != W_KING
            || self.piece_on(self.square(BLACK, KING)) != B_KING
            || (self.ep_square() != Square::NONE
                && self.ep_square().relative_rank(self.side_to_move())
                    != RANK_6)
        {
            panic!("pos: Default");
        }

        if self.count(WHITE, KING) != 1
            || self.count(BLACK, KING) != 1
            || self.attackers_to(self.square(!self.side_to_move(), KING))
                & self.pieces_c(self.side_to_move()) != 0
        {
            panic!("pos_is_ok: Kings");
        }

        if self.pieces_p(PAWN) & (RANK1_BB | RANK8_BB) != 0
            || self.count(WHITE, PAWN) > 8
            || self.count(BLACK, PAWN) > 8
        {
            panic!("pos_is_ok: Pawns");
        }

        for p1 in 1..6 {
            for p2 in 1..6 {
                if p1 != p2
                    && self.pieces_p(PieceType(p1))
                        & self.pieces_p(PieceType(p2)) != 0
                {
                    panic!("pos_is_ok: Bitboards");
                }
            }
        }

        for p in 1..14 {
            if p == 7 || p == 8 {
                continue;
            }
            let pc = Piece(p);
            if self.piece_count[pc.0 as usize] !=
                popcount(self.pieces_cp(pc.color(), pc.piece_type())) as i32
            {
                panic!("pos_is_ok: Pieces {}", p);
            }

            for i in 0..self.piece_count[pc.0 as usize] {
                if self.board
                        [self.piece_list[pc.0 as usize][i as usize].0 as usize]
                        != pc
                    || self.index
                        [self.piece_list[pc.0 as usize][i as usize].0 as usize]
                        != i
                {
                    panic!("pos_is_ok: Index {}, {}", p, i);
                }
            }
        }

        true
    }
}
