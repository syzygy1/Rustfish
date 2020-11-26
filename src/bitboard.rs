// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(dead_code)]

use types::*;
use uci;

use std;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Bitboard(pub u64);

pub fn popcount(bb: Bitboard) -> u32 {
    bb.0.count_ones()
}

pub const ALL_SQUARES: Bitboard = Bitboard(!0u64);
pub const DARK_SQUARES: Bitboard = Bitboard(0xaa55aa55aa55aa55);

pub const FILEA_BB: Bitboard = Bitboard(0x0101010101010101);
pub const FILEB_BB: Bitboard = Bitboard(0x0202020202020202);
pub const FILEC_BB: Bitboard = Bitboard(0x0404040404040404);
pub const FILED_BB: Bitboard = Bitboard(0x0808080808080808);
pub const FILEE_BB: Bitboard = Bitboard(0x1010101010101010);
pub const FILEF_BB: Bitboard = Bitboard(0x2020202020202020);
pub const FILEG_BB: Bitboard = Bitboard(0x4040404040404040);
pub const FILEH_BB: Bitboard = Bitboard(0x8080808080808080);

pub const RANK1_BB: Bitboard = Bitboard(0xff);
pub const RANK2_BB: Bitboard = Bitboard(0xff00);
pub const RANK3_BB: Bitboard = Bitboard(0xff0000);
pub const RANK4_BB: Bitboard = Bitboard(0xff000000);
pub const RANK5_BB: Bitboard = Bitboard(0xff00000000);
pub const RANK6_BB: Bitboard = Bitboard(0xff0000000000);
pub const RANK7_BB: Bitboard = Bitboard(0xff000000000000);
pub const RANK8_BB: Bitboard = Bitboard(0xff00000000000000);

static mut SQUARE_DISTANCE: [[u32; 64]; 64] = [[0; 64]; 64];

static mut SQUARE_BB: [Bitboard; 64] = [Bitboard(0); 64];
static mut FILE_BB: [Bitboard; 8] = [Bitboard(0); 8];
static mut RANK_BB: [Bitboard; 8] = [Bitboard(0); 8];
static mut ADJACENT_FILES_BB: [Bitboard; 8] = [Bitboard(0); 8];
static mut FORWARD_RANKS_BB: [[Bitboard; 8]; 2] = [[Bitboard(0); 8]; 2];
static mut BETWEEN_BB: [[Bitboard; 64]; 64] = [[Bitboard(0); 64]; 64];
static mut LINE_BB: [[Bitboard; 64]; 64] = [[Bitboard(0); 64]; 64];
static mut DISTANCE_RING_BB: [[Bitboard; 8]; 64] = [[Bitboard(0); 8]; 64];
static mut FORWARD_FILE_BB: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
static mut PASSED_PAWN_MASK: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
static mut PAWN_ATTACK_SPAN: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
static mut PSEUDO_ATTACKS: [[Bitboard; 64]; 8] = [[Bitboard(0); 64]; 8];
static mut PAWN_ATTACKS: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];

struct Magics {
    masks: [Bitboard; 64],
    magics: [u64; 64],
    attacks: [&'static [Bitboard]; 64],
}

static mut ROOK_MAGICS: Magics = Magics {
    masks: [Bitboard(0); 64],
    magics: [0; 64],
    attacks: [&[]; 64],
};

static mut BISHOP_MAGICS: Magics = Magics {
    masks: [Bitboard(0); 64],
    magics: [0; 64],
    attacks: [&[]; 64],
};

static mut ATTACKS_TABLE: [Bitboard; 88772] = [Bitboard(0); 88772];

struct MagicInit {
    magic: u64,
    index: u32,
}

macro_rules! M { ($x:expr, $y:expr) => { MagicInit { magic: $x, index: $y } } }

const BISHOP_INIT: [MagicInit; 64] = [
    M!(0x007fbfbfbfbfbfff,  5378),
    M!(0x0000a060401007fc,  4093),
    M!(0x0001004008020000,  4314),
    M!(0x0000806004000000,  6587),
    M!(0x0000100400000000,  6491),
    M!(0x000021c100b20000,  6330),
    M!(0x0000040041008000,  5609),
    M!(0x00000fb0203fff80, 22236),
    M!(0x0000040100401004,  6106),
    M!(0x0000020080200802,  5625),
    M!(0x0000004010202000, 16785),
    M!(0x0000008060040000, 16817),
    M!(0x0000004402000000,  6842),
    M!(0x0000000801008000,  7003),
    M!(0x000007efe0bfff80,  4197),
    M!(0x0000000820820020,  7356),
    M!(0x0000400080808080,  4602),
    M!(0x00021f0100400808,  4538),
    M!(0x00018000c06f3fff, 29531),
    M!(0x0000258200801000, 45393),
    M!(0x0000240080840000, 12420),
    M!(0x000018000c03fff8, 15763),
    M!(0x00000a5840208020,  5050),
    M!(0x0000020008208020,  4346),
    M!(0x0000804000810100,  6074),
    M!(0x0001011900802008,  7866),
    M!(0x0000804000810100, 32139),
    M!(0x000100403c0403ff, 57673),
    M!(0x00078402a8802000, 55365),
    M!(0x0000101000804400, 15818),
    M!(0x0000080800104100,  5562),
    M!(0x00004004c0082008,  6390),
    M!(0x0001010120008020,  7930),
    M!(0x000080809a004010, 13329),
    M!(0x0007fefe08810010,  7170),
    M!(0x0003ff0f833fc080, 27267),
    M!(0x007fe08019003042, 53787),
    M!(0x003fffefea003000,  5097),
    M!(0x0000101010002080,  6643),
    M!(0x0000802005080804,  6138),
    M!(0x0000808080a80040,  7418),
    M!(0x0000104100200040,  7898),
    M!(0x0003ffdf7f833fc0, 42012),
    M!(0x0000008840450020, 57350),
    M!(0x00007ffc80180030, 22813),
    M!(0x007fffdd80140028, 56693),
    M!(0x00020080200a0004,  5818),
    M!(0x0000101010100020,  7098),
    M!(0x0007ffdfc1805000,  4451),
    M!(0x0003ffefe0c02200,  4709),
    M!(0x0000000820806000,  4794),
    M!(0x0000000008403000, 13364),
    M!(0x0000000100202000,  4570),
    M!(0x0000004040802000,  4282),
    M!(0x0004010040100400, 14964),
    M!(0x00006020601803f4,  4026),
    M!(0x0003ffdfdfc28048,  4826),
    M!(0x0000000820820020,  7354),
    M!(0x0000000008208060,  4848),
    M!(0x0000000000808020, 15946),
    M!(0x0000000001002020, 14932),
    M!(0x0000000401002008, 16588),
    M!(0x0000004040404040,  6905),
    M!(0x007fff9fdf7ff813, 16076),
];

const ROOK_INIT: [MagicInit; 64] = [
    M!(0x00280077ffebfffe, 26304),
    M!(0x2004010201097fff, 35520),
    M!(0x0010020010053fff, 38592),
    M!(0x0040040008004002,  8026),
    M!(0x7fd00441ffffd003, 22196),
    M!(0x4020008887dffffe, 80870),
    M!(0x004000888847ffff, 76747),
    M!(0x006800fbff75fffd, 30400),
    M!(0x000028010113ffff, 11115),
    M!(0x0020040201fcffff, 18205),
    M!(0x007fe80042ffffe8, 53577),
    M!(0x00001800217fffe8, 62724),
    M!(0x00001800073fffe8, 34282),
    M!(0x00001800e05fffe8, 29196),
    M!(0x00001800602fffe8, 23806),
    M!(0x000030002fffffa0, 49481),
    M!(0x00300018010bffff,  2410),
    M!(0x0003000c0085fffb, 36498),
    M!(0x0004000802010008, 24478),
    M!(0x0004002020020004, 10074),
    M!(0x0001002002002001, 79315),
    M!(0x0001001000801040, 51779),
    M!(0x0000004040008001, 13586),
    M!(0x0000006800cdfff4, 19323),
    M!(0x0040200010080010, 70612),
    M!(0x0000080010040010, 83652),
    M!(0x0004010008020008, 63110),
    M!(0x0000040020200200, 34496),
    M!(0x0002008010100100, 84966),
    M!(0x0000008020010020, 54341),
    M!(0x0000008020200040, 60421),
    M!(0x0000820020004020, 86402),
    M!(0x00fffd1800300030, 50245),
    M!(0x007fff7fbfd40020, 76622),
    M!(0x003fffbd00180018, 84676),
    M!(0x001fffde80180018, 78757),
    M!(0x000fffe0bfe80018, 37346),
    M!(0x0001000080202001,   370),
    M!(0x0003fffbff980180, 42182),
    M!(0x0001fffdff9000e0, 45385),
    M!(0x00fffefeebffd800, 61659),
    M!(0x007ffff7ffc01400, 12790),
    M!(0x003fffbfe4ffe800, 16762),
    M!(0x001ffff01fc03000,     0),
    M!(0x000fffe7f8bfe800, 38380),
    M!(0x0007ffdfdf3ff808, 11098),
    M!(0x0003fff85fffa804, 21803),
    M!(0x0001fffd75ffa802, 39189),
    M!(0x00ffffd7ffebffd8, 58628),
    M!(0x007fff75ff7fbfd8, 44116),
    M!(0x003fff863fbf7fd8, 78357),
    M!(0x001fffbfdfd7ffd8, 44481),
    M!(0x000ffff810280028, 64134),
    M!(0x0007ffd7f7feffd8, 41759),
    M!(0x0003fffc0c480048,  1394),
    M!(0x0001ffffafd7ffd8, 40910),
    M!(0x00ffffe4ffdfa3ba, 66516),
    M!(0x007fffef7ff3d3da,  3897),
    M!(0x003fffbfdfeff7fa,  3930),
    M!(0x001fffeff7fbfc22, 72934),
    M!(0x0000020408001001, 72662),
    M!(0x0007fffeffff77fd, 56325),
    M!(0x0003ffffbf7dfeec, 66501),
    M!(0x0001ffff9dffa333, 14826),
];

// Compute the attack's index using the 'magic bitboards' approach
fn index_bishop(s: Square, occupied: Bitboard) -> usize {
    unsafe {
        (u64::wrapping_mul((occupied & BISHOP_MAGICS.masks[s.0 as usize]).0,
            BISHOP_MAGICS.magics[s.0 as usize]
        ) >> (64-9)) as usize 
    }
}

fn index_rook(s: Square, occupied: Bitboard) -> usize {
    unsafe {
        (u64::wrapping_mul((occupied & ROOK_MAGICS.masks[s.0 as usize]).0,
            ROOK_MAGICS.magics[s.0 as usize]
        ) >> (64-12)) as usize
    }
}

fn attacks_bb_bishop(s: Square, occupied: Bitboard) -> Bitboard {
    unsafe {
        BISHOP_MAGICS.attacks[s.0 as usize][index_bishop(s, occupied)]
    }
}

fn attacks_bb_rook(s: Square, occupied: Bitboard) -> Bitboard {
    unsafe {
        ROOK_MAGICS.attacks[s.0 as usize][index_rook(s, occupied)]
    }
}

impl std::convert::From<Square> for Bitboard {
    fn from(s: Square) -> Self {
        unsafe { SQUARE_BB[s.0 as usize] }
    }
}

impl Square {
    pub fn bb(self) -> Bitboard {
        Bitboard::from(self)
    }

    pub fn file_bb(self) -> Bitboard {
        file_bb(self.file())
    }

    pub fn rank_bb(self) -> Bitboard {
        unsafe { RANK_BB[self.rank() as usize] }
    }
}

impl std::ops::BitOr<Bitboard> for Bitboard {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Bitboard(self.0 | rhs.0)
    }
}

impl std::ops::BitOr<Square> for Bitboard {
    type Output = Bitboard;
    fn bitor(self, rhs: Square) -> Self {
        self | Bitboard::from(rhs)
    }
}

impl std::ops::BitAnd<Bitboard> for Bitboard {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Bitboard(self.0 & rhs.0)
    }
}

impl std::ops::BitAnd<Square> for Bitboard {
    type Output = Bitboard;
    fn bitand(self, rhs: Square) -> Self {
        self & Bitboard::from(rhs)
    }
}

impl std::ops::BitXor<Bitboard> for Bitboard {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Bitboard(self.0 ^ rhs.0)
    }
}

impl std::ops::BitXor<Square> for Bitboard {
    type Output = Bitboard;
    fn bitxor(self, rhs: Square) -> Self {
        self ^ Bitboard::from(rhs)
    }
}

impl std::ops::Not for Bitboard {
    type Output = Bitboard;
    fn not(self) -> Self {
        Bitboard(!self.0)
    }
}

impl std::ops::Neg for Bitboard {
    type Output = Bitboard;
    fn neg(self) -> Self {
        Bitboard(self.0.wrapping_neg())
    }
}

impl std::ops::Shl<i32> for Bitboard {
    type Output = Bitboard;
    fn shl(self, rhs: i32) -> Self {
        Bitboard(self.0 << rhs)
    }
}

impl std::ops::Shr<i32> for Bitboard {
    type Output = Bitboard;
    fn shr(self, rhs: i32) -> Self {
        Bitboard(self.0 >> rhs)
    }
}

impl<RHS> std::ops::BitOrAssign<RHS> for Bitboard
    where Bitboard: std::ops::BitOr<RHS, Output=Bitboard>
{
    fn bitor_assign(&mut self, rhs: RHS) {
        *self = *self | rhs;
    }
}

impl<RHS> std::ops::BitAndAssign<RHS> for Bitboard
    where Bitboard: std::ops::BitAnd<RHS, Output=Bitboard>
{
    fn bitand_assign(&mut self, rhs: RHS) {
        *self = *self & rhs;
    }
}

impl<RHS> std::ops::BitXorAssign<RHS> for Bitboard
    where Bitboard: std::ops::BitXor<RHS, Output=Bitboard>
{
    fn bitxor_assign(&mut self, rhs: RHS) {
        *self = *self ^ rhs;
    }
}

impl std::cmp::PartialEq<u64> for Bitboard {
    fn eq(&self, rhs: &u64) -> bool {
        debug_assert!(*rhs == 0);
        (*self).0 == *rhs
    }
}

impl std::fmt::Display for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        for s in *self {
            write!(f, "{} ", uci::square(s)).unwrap();
        }
        write!(f, "")
    }
}

pub fn more_than_one(b: Bitboard) -> bool {
    (b.0 & u64::wrapping_sub(b.0, 1)) != 0
}

pub fn lsb(b: Bitboard) -> Square {
    debug_assert!(b != 0);
    Square(u64::trailing_zeros(b.0))
}

pub fn msb(b: Bitboard) -> Square {
    debug_assert!(b != 0);
    Square(63 ^ u64::leading_zeros(b.0))
}

pub fn pop_lsb(b: &mut Bitboard) -> Square {
    let s = lsb(*b);
    b.0 &= u64::wrapping_sub(b.0, 1);
    s
}

pub fn frontmost_sq(c: Color, b: Bitboard) -> Square {
    if c == WHITE { msb(b) } else { lsb(b) }
}

pub fn backmost_sq(c: Color, b: Bitboard) -> Square {
    if c == WHITE { lsb(b) } else { msb(b) }
}

impl Iterator for Bitboard {
    type Item = Square;
    fn next(&mut self) -> Option<Self::Item> {
        if (*self).0 != 0 {
            Some(pop_lsb(self))
        } else {
            None
        }
    }
}

// file_bb() return a bitboard representing all the squares on the given file.

pub fn file_bb(f: File) -> Bitboard {
    unsafe { FILE_BB[f as usize] }
}

// bitboard!(A1, A2, ...) creates a bitboard with squares A1, A2, ...

macro_rules! bitboard {
    () => { Bitboard(0) };
    ($sq:ident) => { bitboard!() | Square::$sq };
    ($sq:ident, $($sqs:ident),+) => { bitboard!($($sqs),*) | Square::$sq };
}

// shift() moves a bitboard one step along direction D. Mainly for pawns.

impl Bitboard {
    pub fn shift(self, d: Direction) -> Bitboard {
        match d {
            NORTH => self << 8,
            SOUTH => self >> 8,
            NORTH_EAST => (self & !FILEH_BB) << 9,
            SOUTH_EAST => (self & !FILEH_BB) >> 7,
            NORTH_WEST => (self & !FILEA_BB) << 7,
            SOUTH_WEST => (self & !FILEA_BB) >> 9,
            _ => Bitboard(0)
        }
    }
}

// adjacent_files_bb() returns a bitboard representing all the squares on
// the adjacent files of the given one.

pub fn adjacent_files_bb(f: File) -> Bitboard {
    unsafe { ADJACENT_FILES_BB[f as usize] }
}

// between_bb() returns a bitboard representing all the squares between the
// two given ones. For instance, between_bb(Square::C4, Square::F7) returns
// a bitboard with the bits for squares d5 and e6 set. If s1 and s2 are not
// on the same rank, file or diagonal, an empty bitboard is returned.

pub fn between_bb(s1: Square, s2: Square) -> Bitboard {
    unsafe { BETWEEN_BB[s1.0 as usize][s2.0 as usize] }
}

// forward_ranks_bb() returns a bitboard representing all the squares on all
// the ranks in front of the given one, from the point of view of the given
// color. For instance, forward_ranks_bb(BLACK, Square::D3) returns the 16
// squares on ranks 1 and 2.

pub fn forward_ranks_bb(c: Color, s: Square) -> Bitboard {
    unsafe { FORWARD_RANKS_BB[c.0 as usize][s.rank() as usize] }
}

// forward_file_bb() returns a bitboard representing all the squares along
// the line in front of the given one, from the point of view of the given
// color.

pub fn forward_file_bb(c: Color, s: Square) -> Bitboard {
    unsafe { FORWARD_FILE_BB[c.0 as usize][s.0 as usize] }
}

// pawn_attack_span() returns a bitboard representing all the squares that
// can be attacked by a pawn of the given color when it moves along its file,
// starting from the given square.

pub fn pawn_attack_span(c: Color, s: Square) -> Bitboard {
    unsafe { PAWN_ATTACK_SPAN[c.0 as usize][s.0 as usize] }
}

// passed_pawn_mask() returns a bitboard mask which can be used to test if a
// pawn of the given color and on the given square is a passed pawn.

pub fn passed_pawn_mask(c: Color, s: Square) -> Bitboard {
    unsafe { PASSED_PAWN_MASK[c.0 as usize][s.0 as usize] }
}

pub fn line_bb(s1: Square, s2: Square) -> Bitboard {
    unsafe { LINE_BB[s1.0 as usize][s2.0 as usize] }
}

// aligned() returns true if the squares s1, s2 and s3 are aligned either on
// a straight or on a diagonal line.

pub fn aligned(s1: Square, s2: Square, s3: Square) -> bool {
    line_bb(s1, s2) & s3 != 0
}

pub fn pseudo_attacks(pt: PieceType, s: Square) -> Bitboard {
    unsafe { PSEUDO_ATTACKS[pt.0 as usize][s.0 as usize] }
}

pub fn pawn_attacks(c: Color, s: Square) -> Bitboard {
    unsafe { PAWN_ATTACKS[c.0 as usize][s.0 as usize] }
}

pub fn distance_ring_bb(s: Square, d: i32) -> Bitboard {
    unsafe { DISTANCE_RING_BB[s.0 as usize][d as usize] }
}

pub trait Distance {
    fn distance(x: Self, y: Self) -> u32;
}

impl Distance for u32 {
    fn distance(x: Self, y: Self) -> u32 {
        if x > y { x - y } else { y - x }
    }
}

impl Distance for Square {
    fn distance(x: Self, y: Self) -> u32 {
        unsafe { SQUARE_DISTANCE[x.0 as usize][y.0 as usize] }
    }
}

// init() initializes various bitboard tables. It is called at startup.

pub fn init() {
    for s in ALL_SQUARES {
        unsafe { SQUARE_BB[s.0 as usize] = Bitboard(1u64) << (s.0 as i32); }
    }

    for f in 0..8 {
        unsafe { FILE_BB[f as usize] = FILEA_BB << f; }
    }

    for r in 0..8 {
        unsafe { RANK_BB[r as usize] = RANK1_BB << (8 * r); }
    }

    for f in 0..8 {
        unsafe {
            let left = if f > FILE_A { file_bb(f - 1) } else { Bitboard(0) };
            let right = if f < FILE_H { file_bb(f + 1) } else { Bitboard(0) };
            ADJACENT_FILES_BB[f as usize] = left | right;
        }
    }

    for r in 0..7 {
        unsafe {
            FORWARD_RANKS_BB[BLACK.0 as usize][(r + 1) as usize] =
                FORWARD_RANKS_BB[BLACK.0 as usize][r as usize]
                | RANK_BB[r as usize];
            FORWARD_RANKS_BB[WHITE.0 as usize][r as usize] =
                !FORWARD_RANKS_BB[BLACK.0 as usize][(r + 1) as usize];
        }
    }

    for &c in [WHITE, BLACK].iter() {
        for s in ALL_SQUARES {
            unsafe {
                FORWARD_FILE_BB[c.0 as usize][s.0 as usize] =
                    FORWARD_RANKS_BB[c.0 as usize][s.rank() as usize]
                    & FILE_BB[s.file() as usize];
                PAWN_ATTACK_SPAN[c.0 as usize][s.0 as usize] =
                    FORWARD_RANKS_BB[c.0 as usize][s.rank() as usize]
                    & ADJACENT_FILES_BB[s.file() as usize];
                PASSED_PAWN_MASK[c.0 as usize][s.0 as usize] =
                    FORWARD_FILE_BB[c.0 as usize][s.0 as usize]
                    | PAWN_ATTACK_SPAN[c.0 as usize][s.0 as usize];
            }
        }
    }

    for s1 in ALL_SQUARES {
        for s2 in ALL_SQUARES {
            if s1 != s2 {
                unsafe {
                    let dist =
                        std::cmp::max(File::distance(s1.file(),s2.file()),
                            Rank::distance(s1.rank(), s2.rank()));
                    SQUARE_DISTANCE[s1.0 as usize][s2.0 as usize] = dist;
                    DISTANCE_RING_BB[s1.0 as usize][dist as usize - 1] |= s2;
                }
            }
        }
    }

    for &c in [WHITE, BLACK].iter() {
        for &pt in [PAWN, KNIGHT, KING].iter() {
            for s in ALL_SQUARES {
                let steps: &[i32] = match pt {
                    PAWN => &[7, 9],
                    KNIGHT => &[6, 10, 15, 17],
                    _ => &[1, 7, 8, 9]
                };
                for &d in steps.iter() {
                    let to = s
                        + if c == WHITE { Direction(d) } else { -Direction(d) };
                    if to.is_ok() && Square::distance(s, to) < 3 {
                        unsafe {
                            if pt == PAWN {
                                PAWN_ATTACKS[c.0 as usize][s.0 as usize] |= to;
                            } else {
                                PSEUDO_ATTACKS[pt.0 as usize][s.0 as usize] |=
                                    to;
                            }
                        }
                    }
                }
            }
        }
    }

    let rook_dirs = [NORTH, EAST, SOUTH, WEST];
    let bishop_dirs = [NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST];

    unsafe {
        init_magics(&mut ROOK_MAGICS, &ROOK_INIT, rook_dirs, index_rook);
        init_magics(&mut BISHOP_MAGICS, &BISHOP_INIT, bishop_dirs,
            index_bishop);
    }

    for s1 in ALL_SQUARES {
        let b_att = attacks_bb(BISHOP, s1, Bitboard(0));
        let r_att = attacks_bb(ROOK  , s1, Bitboard(0));
        unsafe {
            PSEUDO_ATTACKS[BISHOP.0 as usize][s1.0 as usize] = b_att;
            PSEUDO_ATTACKS[ROOK.0   as usize][s1.0 as usize] = r_att;
            PSEUDO_ATTACKS[QUEEN.0  as usize][s1.0 as usize] = b_att | r_att;
        }
        for &pt in [BISHOP, ROOK].iter() {
            for s2 in ALL_SQUARES {
                unsafe {
                    if PSEUDO_ATTACKS[pt.0 as usize][s1.0 as usize] & s2 == 0 {
                        continue;
                    }
                    LINE_BB[s1.0 as usize][s2.0 as usize] =
                        (attacks_bb(pt, s1, Bitboard(0))
                        & attacks_bb(pt, s2, Bitboard(0))) | s1 | s2;
                    BETWEEN_BB[s1.0 as usize][s2.0 as usize] =
                        attacks_bb(pt, s1, s2.bb())
                        & attacks_bb(pt, s2, s1.bb());
                }
            }
        }
    }
}

fn sliding_attack(
    directions: [Direction; 4], sq: Square, occupied: Bitboard
) -> Bitboard {
    let mut attack = Bitboard(0);
    for d in directions.iter() {
        let mut s = sq + *d;
        while s.is_ok() && Square::distance(s, s - *d) == 1 {
            attack |= s;
            if occupied & s != 0 {
                break;
            }
            s += *d;
        }
    }
    attack
}

fn init_magics(
    m: &mut Magics, magic_init: &[MagicInit; 64], dirs: [Direction; 4],
    index: fn(Square, Bitboard) -> usize,
) {
    for s in ALL_SQUARES {
        // Board edges are not considered in the relevant occupancies
        let edges = ((RANK1_BB | RANK8_BB) & !s.rank_bb())
            | ((FILEA_BB | FILEH_BB) & !s.file_bb());

        let mask = sliding_attack(dirs, s, Bitboard(0)) & !edges;

        m.masks[s.0 as usize] = mask;
        m.magics[s.0 as usize] = magic_init[s.0 as usize].magic;

        let base = magic_init[s.0 as usize].index as usize;
        let mut size = 0;

        // Use Carry-Ripler trick to enumerate all subsets of masks[s] and
        // fill the attacks table.
        let mut b = Bitboard(0);
        loop {
            let idx = index(s, b);
            size = std::cmp::max(size, idx + 1);
            unsafe {
                ATTACKS_TABLE[base + idx] = sliding_attack(dirs, s, b);
            }
            b = Bitboard(u64::wrapping_sub(b.0, mask.0)) & mask;
            if b == 0 { break; }
        }

        m.attacks[s.0 as usize] = unsafe { &ATTACKS_TABLE[base..base+size] };
    }
}

// attacks_bb() returns a bitboard representing all the squares attacked by
// a piece of type Pt (bishop or rook) placed on 's'.

pub fn attacks_bb(pt: PieceType, s: Square, occupied: Bitboard) -> Bitboard {
    match pt {
        BISHOP => attacks_bb_bishop(s, occupied),
        ROOK => attacks_bb_rook(s, occupied),
        QUEEN => attacks_bb_bishop(s, occupied) | attacks_bb_rook(s, occupied),
        _ => pseudo_attacks(pt, s),
    }
}
