// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(dead_code)]

use std;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Key(pub u64);

impl std::ops::BitXor<Key> for Key {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self { Key(self.0 ^ rhs.0) }
}

impl std::ops::BitXorAssign<Key> for Key {
    fn bitxor_assign(&mut self, rhs: Key) { *self = *self ^ rhs; }
}

impl std::fmt::Display for Key {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{:X}", self.0)
    }
}

pub const MAX_MOVES: usize = 256;
pub const MAX_PLY: i32 = 128;
pub const MAX_MATE_PLY : i32 = 128;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Color(pub u32);

pub const WHITE: Color = Color(0);
pub const BLACK: Color = Color(1);

impl std::ops::Not for Color {
    type Output = Color;
    fn not(self) -> Self { Color(self.0 ^ 1) }
}

impl std::ops::BitXor<bool> for Color {
    type Output = Self;
    fn bitxor(self, rhs: bool) -> Self { Color(self.0 ^ (rhs as u32)) }
}

impl Iterator for Color {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
        let sq = self.0;
        self.0 += 1;
        Some(Color(sq))
    }
}

pub struct White;
pub struct Black;

pub trait ColorTrait {
    type KingSide: CastlingRightTrait;
    type QueenSide: CastlingRightTrait;
    const COLOR: Color;
}

impl ColorTrait for White {
    type KingSide = WhiteOO;
    type QueenSide = WhiteOOO;
    const COLOR: Color = WHITE;
}

impl ColorTrait for Black {
    type KingSide = BlackOO;
    type QueenSide = BlackOOO;
    const COLOR: Color = BLACK;
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CastlingSide {
    KING,
    QUEEN
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct CastlingRight(pub u32);

pub const NO_CASTLING : CastlingRight = CastlingRight(0);
pub const WHITE_OO    : CastlingRight = CastlingRight(1);
pub const WHITE_OOO   : CastlingRight = CastlingRight(2);
pub const BLACK_OO    : CastlingRight = CastlingRight(4);
pub const BLACK_OOO   : CastlingRight = CastlingRight(8);
pub const ANY_CASTLING: CastlingRight = CastlingRight(15);

pub trait CastlingRightTrait {
    const CR: CastlingRight;
}

pub struct WhiteOO;
pub struct WhiteOOO;
pub struct BlackOO;
pub struct BlackOOO;

impl CastlingRightTrait for WhiteOO {
    const CR: CastlingRight = WHITE_OO;
}

impl CastlingRightTrait for WhiteOOO {
    const CR: CastlingRight = WHITE_OOO;
}

impl CastlingRightTrait for BlackOO {
    const CR: CastlingRight = BLACK_OO;
}

impl CastlingRightTrait for BlackOOO {
    const CR: CastlingRight = BLACK_OOO;
}

impl CastlingRight {
    pub fn make(c: Color, cs: CastlingSide) -> CastlingRight {
        use types::CastlingSide::*;
        match (c, cs) {
            (WHITE, KING) => WHITE_OO,
            (WHITE, _   ) => WHITE_OOO,
            (_    , KING) => BLACK_OO,
            (_    , _   ) => BLACK_OOO
        }
     }
}

impl std::ops::BitOr<CastlingSide> for Color {
    type Output = CastlingRight;
    fn bitor(self, rhs: CastlingSide) -> CastlingRight {
        CastlingRight(1u32 << ((rhs as u32) + 2 * self.0))
    }
}

impl std::ops::BitAnd<CastlingRight> for CastlingRight {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self { CastlingRight(self.0 & rhs.0) }
}

impl std::ops::BitOr<CastlingRight> for CastlingRight {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self { CastlingRight(self.0 | rhs.0) }
}

impl std::ops::BitAndAssign<CastlingRight> for CastlingRight {
    fn bitand_assign(&mut self, rhs: Self) { *self = *self & rhs; }
}

impl std::ops::BitOrAssign<CastlingRight> for CastlingRight {
    fn bitor_assign(&mut self, rhs: Self) { *self = *self | rhs; }
}

impl std::ops::Not for CastlingRight {
    type Output = CastlingRight;
    fn not(self) -> Self { CastlingRight(!self.0) }
}

impl std::cmp::PartialEq<u32> for CastlingRight {
    fn eq(&self, rhs: &u32) -> bool {
        debug_assert!(*rhs == 0);
        self.0 == *rhs
    }
}

pub type Phase = i32;

pub const PHASE_ENDGAME: Phase = 0;
pub const PHASE_MIDGAME: Phase = 128;

pub const MG: usize = 0;
pub const EG: usize = 1;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ScaleFactor(pub i32);

impl ScaleFactor {
    pub const DRAW   : ScaleFactor = ScaleFactor(0);
    pub const ONEPAWN: ScaleFactor = ScaleFactor(48);
    pub const NORMAL : ScaleFactor = ScaleFactor(64);
    pub const MAX    : ScaleFactor = ScaleFactor(128);
    pub const NONE   : ScaleFactor = ScaleFactor(255);
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Bound(pub u32);

impl Bound {
    pub const NONE : Bound = Bound(0);
    pub const UPPER: Bound = Bound(1);
    pub const LOWER: Bound = Bound(2);
    pub const EXACT: Bound = Bound(3);
}

impl std::ops::BitAnd<Bound> for Bound {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self { Bound(self.0 & rhs.0) }
}

impl std::ops::BitOr<Bound> for Bound {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self { Bound(self.0 | rhs.0) }
}

impl std::cmp::PartialEq<u32> for Bound {
    fn eq(&self, rhs: &u32) -> bool {
        debug_assert!(*rhs == 0);
        self.0 == *rhs
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PieceType(pub u32);

pub const NO_PIECE_TYPE: PieceType = PieceType(0);

pub const PAWN  : PieceType = PieceType(1);
pub const KNIGHT: PieceType = PieceType(2);
pub const BISHOP: PieceType = PieceType(3);
pub const ROOK  : PieceType = PieceType(4);
pub const QUEEN : PieceType = PieceType(5);
pub const KING  : PieceType = PieceType(6);

pub const QUEEN_DIAGONAL: PieceType = PieceType(7);

pub const ALL_PIECES: PieceType = PieceType(0);

pub struct Pawn;
pub struct Knight;
pub struct Bishop;
pub struct Rook;
pub struct Queen;
pub struct King;

pub trait PieceTypeTrait {
    const TYPE: PieceType;
}

impl PieceTypeTrait for Pawn {
    const TYPE: PieceType = PAWN;
}

impl PieceTypeTrait for Knight {
    const TYPE: PieceType = KNIGHT;
}

impl PieceTypeTrait for Bishop {
    const TYPE: PieceType = BISHOP;
}

impl PieceTypeTrait for Rook {
    const TYPE: PieceType = ROOK;
}

impl PieceTypeTrait for Queen {
    const TYPE: PieceType = QUEEN;
}

impl PieceTypeTrait for King {
    const TYPE: PieceType = KING;
}



#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Piece(pub u32);

pub const NO_PIECE: Piece = Piece(0);

pub const W_PAWN  : Piece = Piece(1);
pub const W_KNIGHT: Piece = Piece(2);
pub const W_BISHOP: Piece = Piece(3);
pub const W_ROOK  : Piece = Piece(4);
pub const W_QUEEN : Piece = Piece(5);
pub const W_KING  : Piece = Piece(6);

pub const B_PAWN  : Piece = Piece(9);
pub const B_KNIGHT: Piece = Piece(10);
pub const B_BISHOP: Piece = Piece(11);
pub const B_ROOK  : Piece = Piece(12);
pub const B_QUEEN : Piece = Piece(13);
pub const B_KING  : Piece = Piece(14);

impl Piece {
    pub fn piece_type(self) -> PieceType { PieceType(self.0 & 7) }

    pub fn color(self) -> Color { Color(self.0 >> 3) }

    pub fn make(c: Color, pt: PieceType) -> Piece { Piece((c.0 << 3) + pt.0) }
}

impl Iterator for Piece {
    type Item = Self;
    fn next(&mut self) -> Option<Self::Item> {
        let pc = self.0;
        self.0 += 1;
        Some(Piece(pc))
    }
}

impl std::ops::Not for Piece {
    type Output = Self;
    fn not(self) -> Self { Piece(self.0 ^ 8) }
}

impl std::ops::BitXor<bool> for Piece {
    type Output = Self;
    fn bitxor(self, rhs: bool) -> Self { Piece(self.0 ^ ((rhs as u32) << 3)) }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub struct Depth(pub i32);

impl std::ops::Add<Depth> for Depth {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Depth(self.0 + rhs.0) }
}

impl std::ops::Sub<Depth> for Depth {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self { Depth(self.0 - rhs.0) }
}

impl std::ops::AddAssign<Depth> for Depth {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl std::ops::SubAssign<Depth> for Depth {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl std::ops::Mul<i32> for Depth {
    type Output = Self;
    fn mul(self, rhs: i32) -> Self { Depth(self.0 * rhs) }
}

impl std::ops::Mul<Depth> for i32 {
    type Output = Depth;
    fn mul(self, rhs: Depth) -> Depth { Depth(self * rhs.0) }
}

impl std::ops::Div<Depth> for Depth {
    type Output = i32;
    fn div(self, rhs: Depth) -> i32 { self.0 / rhs.0 }
}

pub const ONE_PLY: Depth = Depth(1);

pub const DEPTH_ZERO         : Depth = Depth( 0 * ONE_PLY.0);
pub const DEPTH_QS_CHECKS    : Depth = Depth( 0 * ONE_PLY.0);
pub const DEPTH_QS_NO_CHECKS : Depth = Depth(-1 * ONE_PLY.0);
pub const DEPTH_QS_RECAPTURES: Depth = Depth(-5 * ONE_PLY.0);

pub const DEPTH_NONE: Depth = Depth(-6 * ONE_PLY.0);
pub const DEPTH_MAX : Depth = Depth(MAX_PLY * ONE_PLY.0);

impl Depth {
    pub const ZERO         : Depth = Depth( 0 * ONE_PLY.0);
    pub const QS_CHECKS    : Depth = Depth( 0 * ONE_PLY.0);
    pub const QS_NO_CHECKS : Depth = Depth(-1 * ONE_PLY.0);
    pub const QS_RECAPTURES: Depth = Depth(-5 * ONE_PLY.0);

    pub const NONE: Depth = Depth(-6 * ONE_PLY.0);
    pub const MAX : Depth = Depth(MAX_PLY * ONE_PLY.0);
}

pub type File = u32;
pub type Rank = u32;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Square(pub u32);

pub const FILE_A: File = 0;
pub const FILE_B: File = 1;
pub const FILE_C: File = 2;
pub const FILE_D: File = 3;
pub const FILE_E: File = 4;
pub const FILE_F: File = 5;
pub const FILE_G: File = 6;
pub const FILE_H: File = 7;

pub const RANK_1: Rank = 0;
pub const RANK_2: Rank = 1;
pub const RANK_3: Rank = 2;
pub const RANK_4: Rank = 3;
pub const RANK_5: Rank = 4;
pub const RANK_6: Rank = 5;
pub const RANK_7: Rank = 6;
pub const RANK_8: Rank = 7;

pub fn relative_rank(c: Color, r: Rank) -> Rank {
    r ^ (c.0 * 7)
}

impl Square {
    pub const A1: Square = Square(0);
    pub const B1: Square = Square(1);
    pub const C1: Square = Square(2);
    pub const D1: Square = Square(3);
    pub const E1: Square = Square(4);
    pub const F1: Square = Square(5);
    pub const G1: Square = Square(6);
    pub const H1: Square = Square(7);
    pub const A2: Square = Square(8);
    pub const B2: Square = Square(9);
    pub const C2: Square = Square(10);
    pub const D2: Square = Square(11);
    pub const E2: Square = Square(12);
    pub const F2: Square = Square(13);
    pub const G2: Square = Square(14);
    pub const H2: Square = Square(15);
    pub const A3: Square = Square(16);
    pub const B3: Square = Square(17);
    pub const C3: Square = Square(18);
    pub const D3: Square = Square(19);
    pub const E3: Square = Square(20);
    pub const F3: Square = Square(21);
    pub const G3: Square = Square(22);
    pub const H3: Square = Square(23);
    pub const A4: Square = Square(24);
    pub const B4: Square = Square(25);
    pub const C4: Square = Square(26);
    pub const D4: Square = Square(27);
    pub const E4: Square = Square(28);
    pub const F4: Square = Square(29);
    pub const G4: Square = Square(30);
    pub const H4: Square = Square(31);
    pub const A5: Square = Square(32);
    pub const B5: Square = Square(33);
    pub const C5: Square = Square(34);
    pub const D5: Square = Square(35);
    pub const E5: Square = Square(36);
    pub const F5: Square = Square(37);
    pub const G5: Square = Square(38);
    pub const H5: Square = Square(39);
    pub const A6: Square = Square(40);
    pub const B6: Square = Square(41);
    pub const C6: Square = Square(42);
    pub const D6: Square = Square(43);
    pub const E6: Square = Square(44);
    pub const F6: Square = Square(45);
    pub const G6: Square = Square(46);
    pub const H6: Square = Square(47);
    pub const A7: Square = Square(48);
    pub const B7: Square = Square(49);
    pub const C7: Square = Square(50);
    pub const D7: Square = Square(51);
    pub const E7: Square = Square(52);
    pub const F7: Square = Square(53);
    pub const G7: Square = Square(54);
    pub const H7: Square = Square(55);
    pub const A8: Square = Square(56);
    pub const B8: Square = Square(57);
    pub const C8: Square = Square(58);
    pub const D8: Square = Square(59);
    pub const E8: Square = Square(60);
    pub const F8: Square = Square(61);
    pub const G8: Square = Square(62);
    pub const H8: Square = Square(63);

    pub const NONE: Square = Square(64);

    pub fn file(self) -> File {
        self.0 & 7
    }

    pub fn rank(self) -> Rank {
        self.0 >> 3
    }

    pub fn relative(self, c: Color) -> Self {
        Square(self.0 ^ (c.0 * 56))
    }

    pub fn relative_rank(self, c: Color) -> Rank {
        relative_rank(c, self.rank())
    }

    pub fn is_ok(self) -> bool {
        self >= Square::A1 && self <= Square::H8
    }

    pub fn make(f: File, r: Rank) -> Square {
        Square((r << 3) | f)
    }
}

pub fn relative_square(c: Color, s: Square) -> Square {
    s.relative(c)
}

impl std::ops::Not for Square {
    type Output = Self;
    fn not(self) -> Self { Square(self.0 ^ Square::A8.0) }
}

impl std::ops::BitXor<bool> for Square {
    type Output = Self;
    fn bitxor(self, rhs: bool) -> Self {
        Square(self.0 ^ if rhs { 0x38 } else { 0 })
    }
}

impl Iterator for Square {
    type Item = Self;
    fn next(&mut self) -> Option<Self::Item> {
        let sq = self.0;
        *self = Square(sq + 1);
        Some(Square(sq))
    }
}

#[derive(Clone, Copy)]
pub struct Squares {
    pub start: Square,
    pub end: Square
}

impl Iterator for Squares {
    type Item = Square;
    fn next(&mut self) -> Option<Self::Item> {
        let s = self.start;
        if s != self.end {
            self.start += Direction(1);
            Some(s)
        } else {
            None
        }
    }
}

pub struct SquareList<'a> {
    list: &'a [Square],
    idx: usize
}

impl<'a> SquareList<'a> {
    pub fn construct(list: &'a [Square]) -> SquareList<'a> {
        SquareList { list: list, idx: 0 }
    }
}

impl<'a> Iterator for SquareList<'a> {
    type Item = Square;
    fn next(&mut self) -> Option<Self::Item> {
        let s = self.list[self.idx];
        if s != Square::NONE {
            self.idx += 1;
            Some(s)
        } else {
            None
        }
    }
}

pub fn opposite_colors(s1: Square, s2: Square) -> bool {
    let s = s1.0 ^ s2.0;
    (((s >> 3) ^ s) & 1) != 0
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Direction(pub i32);

impl std::ops::Neg for Direction {
    type Output = Self;
    fn neg(self) -> Self { Direction(-self.0) }
}

pub const NORTH: Direction = Direction( 8);
pub const EAST : Direction = Direction( 1);
pub const SOUTH: Direction = Direction(-8);
pub const WEST : Direction = Direction(-1);

pub const NORTH_EAST: Direction = Direction( 9);
pub const NORTH_WEST: Direction = Direction( 7);
pub const SOUTH_EAST: Direction = Direction(-7);
pub const SOUTH_WEST: Direction = Direction(-9);

impl std::ops::Add<Direction> for Direction {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Direction(self.0 + rhs.0) }
}

impl std::ops::Add<Direction> for Square {
    type Output = Square;
    fn add(self, rhs: Direction) -> Self {
        Square(u32::wrapping_add(self.0, rhs.0 as u32))
    }
}

impl std::ops::Sub<Direction> for Square {
    type Output = Square;
    fn sub(self, rhs: Direction) -> Self {
        Square(u32::wrapping_sub(self.0, rhs.0 as u32))
    }
}

impl std::ops::AddAssign<Direction> for Square {
    fn add_assign(&mut self, rhs: Direction) { *self = *self + rhs; }
}

impl std::ops::SubAssign<Direction> for Square {
    fn sub_assign(&mut self, rhs: Direction) { *self = *self - rhs; }
}

impl std::ops::Mul<Direction> for i32 {
    type Output = Direction;
    fn mul(self, rhs: Direction) -> Direction { Direction(self * rhs.0) }
}

pub fn pawn_push(c: Color) -> Direction {
    match c {
        WHITE => NORTH,
        _     => SOUTH
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MoveType(pub u32);

pub const NORMAL    : MoveType = MoveType(0);
pub const PROMOTION : MoveType = MoveType(1 << 14);
pub const ENPASSANT : MoveType = MoveType(2 << 14);
pub const CASTLING  : MoveType = MoveType(3 << 14);

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Move(pub u32);

impl Move {
    pub const NONE : Move = Move(0);
    pub const NULL : Move = Move(65);

    pub fn from(self) -> Square {
        Square((self.0 >> 6) & 0x3f)
    }

    pub fn to(self) -> Square {
        Square(self.0 & 0x3f)
    }

    pub fn from_to(self) -> u32 {
        self.0 & 0xfff
    }

    pub fn move_type(self) -> MoveType {
        MoveType(self.0 & (3 << 14))
    }

    pub fn promotion_type(self) -> PieceType {
        PieceType(((self.0 >> 12) & 3) + KNIGHT.0)
    }

    pub fn is_ok(self) -> bool {
        self.from() != self.to()
    }

    pub fn make(from: Square, to: Square) -> Move {
        Move((from.0 << 6) + to.0)
    }

    pub fn make_prom(from: Square, to: Square, pt: PieceType) -> Move {
        Move(PROMOTION.0 + ((pt.0 - KNIGHT.0) << 12) + (from.0 << 6) + to.0)
    }

    pub fn make_special(mt: MoveType, from: Square, to: Square) -> Move {
        Move(mt.0 + (from.0 << 6) + to.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Value(pub i32);

impl Value {
    pub const ZERO     : Value = Value(0);
    pub const DRAW     : Value = Value(0);
    pub const KNOWN_WIN: Value = Value(10000);
    pub const MATE     : Value = Value(32000);
    pub const INFINITE : Value = Value(32001);
    pub const NONE     : Value = Value(32002);

    pub const MATE_IN_MAX_PLY : Value =
        Value( Value::MATE.0 - MAX_MATE_PLY - MAX_PLY);
    pub const MATED_IN_MAX_PLY: Value =
        Value(-Value::MATE.0 + MAX_MATE_PLY + MAX_PLY);

    pub fn abs(self) -> Value {
        Value(self.0.abs())
    }
}

#[allow(non_upper_case_globals)]
pub const PawnValueMg  : Value = Value(171);
#[allow(non_upper_case_globals)]
pub const KnightValueMg: Value = Value(764);
#[allow(non_upper_case_globals)]
pub const BishopValueMg: Value = Value(826);
#[allow(non_upper_case_globals)]
pub const RookValueMg  : Value = Value(1282);
#[allow(non_upper_case_globals)]
pub const QueenValueMg : Value = Value(2526);

#[allow(non_upper_case_globals)]
pub const PawnValueEg  : Value = Value(240);
#[allow(non_upper_case_globals)]
pub const KnightValueEg: Value = Value(848);
#[allow(non_upper_case_globals)]
pub const BishopValueEg: Value = Value(891);
#[allow(non_upper_case_globals)]
pub const RookValueEg  : Value = Value(1373);
#[allow(non_upper_case_globals)]
pub const QueenValueEg : Value = Value(2646);

pub const MIDGAME_LIMIT : Value = Value(15258);
pub const ENDGAME_LIMIT : Value = Value(3915);

const PIECE_VALUE: [[Value; 16]; 2] = [
    [ Value::ZERO, PawnValueMg, KnightValueMg, BishopValueMg,
      RookValueMg, QueenValueMg, Value::ZERO, Value::ZERO,
      Value::ZERO, PawnValueMg, KnightValueMg, BishopValueMg,
      RookValueMg, QueenValueMg, Value::ZERO, Value::ZERO ],
    [ Value::ZERO, PawnValueEg, KnightValueEg, BishopValueEg,
      RookValueEg, QueenValueEg, Value::ZERO, Value::ZERO,
      Value::ZERO, PawnValueEg, KnightValueEg, BishopValueEg,
      RookValueEg, QueenValueEg, Value::ZERO, Value::ZERO ]
];

pub fn piece_value(phase: usize, pc: Piece) -> Value {
    PIECE_VALUE[phase][pc.0 as usize]
}

impl std::ops::Neg for Value {
    type Output = Self;
    fn neg(self) -> Self { Value(-self.0) }
}

impl std::ops::Add<Value> for Value {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Value(self.0 + rhs.0) }
}

impl std::ops::Add<i32> for Value {
    type Output = Self;
    fn add(self, rhs: i32) -> Self { self + Value(rhs) }
}

impl std::ops::Sub<i32> for Value {
    type Output = Self;
    fn sub(self, rhs: i32) -> Self { self - Value(rhs) }
}

impl std::ops::Sub<Value> for Value {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self { Value(self.0 - rhs.0) }
}

impl std::ops::AddAssign<Value> for Value {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl std::ops::AddAssign<i32> for Value {
    fn add_assign(&mut self, rhs: i32) { *self = *self + rhs; }
}

impl std::ops::SubAssign<Value> for Value {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl std::ops::SubAssign<i32> for Value {
    fn sub_assign(&mut self, rhs: i32) { *self = *self - rhs; }
}

impl std::ops::Mul<i32> for Value {
    type Output = Self;
    fn mul(self, rhs: i32) -> Self { Value(self.0 * rhs) }
}

impl std::ops::MulAssign<i32> for Value {
    fn mul_assign(&mut self, rhs: i32) { *self = *self * rhs; }
}

impl std::ops::Mul<Value> for i32 {
    type Output = Value;
    fn mul(self, rhs: Value) -> Value { Value(self * rhs.0) }
}

impl std::ops::Div<i32> for Value {
    type Output = Self;
    fn div(self, rhs: i32) -> Self { Value(self.0 / rhs) }
}

impl std::ops::DivAssign<i32> for Value {
    fn div_assign(&mut self, rhs: i32) { *self = *self / rhs; }
}

impl std::ops::Div<Value> for Value {
    type Output = i32;
    fn div(self, rhs: Self) -> i32 { self.0 / rhs.0 }
}

pub fn mate_in(ply: i32) -> Value {
    Value::MATE - ply
}

pub fn mated_in(ply: i32) -> Value {
    -Value::MATE + ply
}

#[derive(Clone, Copy)]
pub struct Score(pub i32);

impl Score {
    pub const ZERO: Score = Score(0);

    pub fn eg(self) -> Value {
        Value((((self.0 + 0x8000) >> 16) as i16) as i32)
    }

    pub fn mg(self) -> Value {
        Value((self.0 as i16) as i32)
    }

    pub fn make(mg: i32, eg: i32) -> Self {
        Score((eg << 16) + mg)
    }
}

impl std::ops::Add<Score> for Score {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Score(self.0 + rhs.0) }
}

impl std::ops::AddAssign<Score> for Score {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl std::ops::Sub<Score> for Score {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self { Score(self.0 - rhs.0) }
}

impl std::ops::SubAssign<Score> for Score {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl std::ops::Neg for Score {
    type Output = Self;
    fn neg(self) -> Self { Score(-self.0) }
}

impl std::ops::Mul<i32> for Score {
    type Output = Self;
    fn mul(self, rhs: i32) -> Self {
        Score::make(rhs * self.mg().0, rhs * self.eg().0)
    }
}

pub struct True {}
pub struct False {}

pub trait Bool {
    const BOOL: bool;
}

impl Bool for True {
    const BOOL: bool = true;
}

impl Bool for False {
    const BOOL: bool = false;
}
