// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(dead_code)]

use misc;
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

pub static mut SQUARE_DISTANCE: [[u32; 64]; 64] = [[0; 64]; 64];

pub static mut SQUARE_BB: [Bitboard; 64] = [Bitboard(0); 64];
pub static mut FILE_BB: [Bitboard; 8] = [Bitboard(0); 8];
pub static mut RANK_BB: [Bitboard; 8] = [Bitboard(0); 8];
pub static mut ADJACENT_FILES_BB: [Bitboard; 8] = [Bitboard(0); 8];
pub static mut FORWARD_RANKS_BB: [[Bitboard; 8]; 2] = [[Bitboard(0); 8]; 2];
pub static mut BETWEEN_BB: [[Bitboard; 64]; 64] = [[Bitboard(0); 64]; 64];
pub static mut LINE_BB: [[Bitboard; 64]; 64] = [[Bitboard(0); 64]; 64];
pub static mut DISTANCE_RING_BB: [[Bitboard; 8]; 64] = [[Bitboard(0); 8]; 64];
pub static mut FORWARD_FILE_BB: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
pub static mut PASSED_PAWN_MASK: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
pub static mut PAWN_ATTACK_SPAN: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];
pub static mut PSEUDO_ATTACKS: [[Bitboard; 64]; 8] = [[Bitboard(0); 64]; 8];
pub static mut PAWN_ATTACKS: [[Bitboard; 64]; 2] = [[Bitboard(0); 64]; 2];

// Magic holds all data relevant to magic bitboards for a single square
#[derive(Copy, Clone)]
struct Magic {
    mask: Bitboard,
    magic: u64,
    attacks: &'static [Bitboard],
    shift: u32
}

// Compute the attack's index using the 'magic bitboards' approach
impl Magic {
    fn index(&self, occupied: Bitboard) -> usize {
        (u64::wrapping_mul((occupied & self.mask).0, self.magic) >> self.shift) as usize
    }
}

static mut ROOK_TABLE: [Bitboard; 0x19000] = [Bitboard(0); 0x19000];
static mut BISHOP_TABLE: [Bitboard; 0x1480] = [Bitboard(0); 0x1480];

static mut ROOK_MAGICS: [Magic; 64] = unsafe { [Magic {mask: Bitboard(0), magic: 0, attacks: &ROOK_TABLE, shift: 0}; 64] };
static mut BISHOP_MAGICS: [Magic; 64] = unsafe { [Magic {mask: Bitboard(0), magic: 0, attacks: &BISHOP_TABLE, shift: 0}; 64] };

impl std::convert::From<Square> for Bitboard {
    fn from(s: Square) -> Self {
        unsafe { SQUARE_BB[s.0 as usize] }
    }
}

impl Square {
    pub fn bb(self) -> Bitboard {
        Bitboard::from(self)
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

// rank_bb() and file_bb() return a bitboard representing all the squares
// on the given file or rank.

pub fn rank_bb(r: Rank) -> Bitboard {
    unsafe { RANK_BB[r as usize] }
}

pub fn file_bb(f: File) -> Bitboard {
    unsafe { FILE_BB[f as usize] }
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
            ADJACENT_FILES_BB[f as usize] =
                (if f > FILE_A { FILE_BB[(f - 1) as usize] } else { Bitboard(0) })
                | (if f < FILE_H { FILE_BB[(f + 1) as usize] } else { Bitboard(0) });
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

    for c in WHITE.take(2) {
        for s in ALL_SQUARES {
            unsafe {
                FORWARD_FILE_BB[c.0 as usize][s.0 as usize] = FORWARD_RANKS_BB[c.0 as usize][s.rank() as usize] & FILE_BB[s.file() as usize];
                PAWN_ATTACK_SPAN[c.0 as usize][s.0 as usize] = FORWARD_RANKS_BB[c.0 as usize][s.rank() as usize] & ADJACENT_FILES_BB[s.file() as usize];
                PASSED_PAWN_MASK[c.0 as usize][s.0 as usize] = FORWARD_FILE_BB[c.0 as usize][s.0 as usize] | PAWN_ATTACK_SPAN[c.0 as usize][s.0 as usize];
            }
        }
    }

    for s1 in ALL_SQUARES {
        for s2 in ALL_SQUARES {
            if s1 != s2 {
                unsafe {
                    SQUARE_DISTANCE[s1.0 as usize][s2.0 as usize] = std::cmp::max(File::distance(s1.file(), s2.file()), Rank::distance(s1.rank(), s2.rank()));
                    DISTANCE_RING_BB[s1.0 as usize][(SQUARE_DISTANCE[s1.0 as usize][s2.0 as usize] - 1) as usize] |= s2;
                }
            }
        }
    }

    for c in WHITE.take(2) {
        for pt in vec![PAWN, KNIGHT, KING] {
            for s in Square::A1.take(64) {
                let steps = match pt {
                    PAWN => vec![7, 9],
                    KNIGHT => vec![6, 10, 15, 17],
                    _ => vec![1, 7, 8, 9]
                };
                for d in steps {
                    let to = s
                        + if c == WHITE { Direction(d) } else { -Direction(d) };
                    if to.is_ok() && Square::distance(s, to) < 3 {
                        if pt == PAWN {
                            unsafe { PAWN_ATTACKS[c.0 as usize][s.0 as usize] |= to; }
                        } else {
                            unsafe { PSEUDO_ATTACKS[pt.0 as usize][s.0 as usize] |= to; }
                        }
                    }
                }
            }
        }
    }

    let rook_dirs = vec![NORTH, EAST, SOUTH, WEST];
    let bishop_dirs = vec![NORTH_EAST, SOUTH_EAST, SOUTH_WEST, NORTH_WEST];

    unsafe {
        init_magics(&mut ROOK_TABLE, &mut ROOK_MAGICS, rook_dirs);
        init_magics(&mut BISHOP_TABLE, &mut BISHOP_MAGICS, bishop_dirs);
    }

    for s1 in ALL_SQUARES {
        let b_att = attacks_bb(BISHOP, s1, Bitboard(0));
        let r_att = attacks_bb(ROOK  , s1, Bitboard(0));
        unsafe {
            PSEUDO_ATTACKS[BISHOP.0 as usize][s1.0 as usize] = b_att;
            PSEUDO_ATTACKS[ROOK.0   as usize][s1.0 as usize] = r_att;
            PSEUDO_ATTACKS[QUEEN.0  as usize][s1.0 as usize] = b_att | r_att;
        }
        for pt in vec![BISHOP, ROOK] {
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
    directions: &Vec<Direction>, sq: Square, occupied: Bitboard
) -> Bitboard {
    let mut attack = Bitboard(0);
    for d in directions {
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

// init_magics() computes all rook and bishop attacks at startup. Magic
// bitboards are used to look up attacks of sliding pieces. As a reference
// see chessprogramming.wikispace.com/Magic+Bitboards. In particular, here
// we use the so-called "fancy" approach.

fn init_magics(
    table: &'static mut [Bitboard], magics: &'static mut [Magic; 64],
    directions: Vec<Direction>
) {
    // Optimal PRNG seeds to pick the correct magics in the shortest time
    let seeds = vec![
        vec![8977, 44560, 54343, 38998,  5731, 95205, 104912, 17020],
        vec![ 728, 10316, 55013, 32803, 12281, 15100,  16645,   255]
    ];

    let mut occupancy: [Bitboard; 4096] = [Bitboard(0); 4096];
    let mut reference: [Bitboard; 4096] = [Bitboard(0); 4096];
    let mut epoch: [i32; 4096] = [0; 4096];
    let mut cnt = 0;
    let mut table_idx: usize = 0;
    let mut sizes: [usize; 64] = [0; 64];

    for s in ALL_SQUARES {
        // Board edges are not considered in the relevant occupancies
        let edges =
            ((RANK1_BB | RANK8_BB) & !rank_bb(s.rank()))
            | ((FILEA_BB | FILEH_BB) & !file_bb(s.file()));

        // Given a square 's', the mask is the bitboard of sliding attacks
        // from 's' computed on an empty board. The index must be big enough
        // to contain all the attacks for each possible subset of the mask
        // and so is 2 to the power the number of 1s of the mask. Hence we
        // deduce the size of the shift to apply to the 64 or 32 bits word
        // to get the index.
        let m = &mut magics[s.0 as usize];
        m.mask = sliding_attack(&directions, s, Bitboard(0)) & !edges;
        m.shift = 64 - popcount(m.mask);

        // Usr Carry-Ripler trick to enumerate all subsets of masks[s] and
        // store the corresponding sliding attack bitboard in reference[].
        let mut b = Bitboard(0);
        let mut size: usize = 0;
        loop {
            occupancy[size] = b;
            reference[size] = sliding_attack(&directions, s, b);
            size += 1;
            b = Bitboard(u64::wrapping_sub(b.0, m.mask.0) & m.mask.0);
            if b == 0 { break; }
        }
        let mut rng = misc::Prng::new(seeds[1][s.rank() as usize]);
        let mut i: usize;
        loop {
            loop {
                m.magic = rng.sparse_rand();
                if (u64::wrapping_mul(m.magic, m.mask.0) >> 56).count_ones()
                    >= 6
                {
                    break;
                }
            }

            // A good magic must map every possible occupancy to an index that
            // looks up the correct sliding attack in the attack[s] database.
            // Note that we build up the database for square 's' as a side
            // effect of verifying the magic. Keep track of the attempt count
            // and save it in epoch[], little speed-up trick to avoid resetting
            // m.attacks[] after every failed attempt.
            cnt += 1;
            i = 0;
            loop {
                let idx = m.index(occupancy[i]);
                if epoch[idx] < cnt {
                    epoch[idx] = cnt;
                    table[table_idx + idx] = reference[i];
                } else if table[table_idx + idx] != reference[i] {
                    break;
                }
                i += 1;
                if i >= size {
                    break;
                }
            }
            if i >= size {
                break;
            }
        }
        sizes[s.0 as usize] = size;
        table_idx += size;
    }
    table_idx = 0;
    for s in ALL_SQUARES {
        let size = sizes[s.0 as usize];
        magics[s.0 as usize].attacks = &table[table_idx..table_idx+size];
        table_idx += size;
    }
}

// attacks_bb() returns a bitboard representing all the squares attacked by
// a piece of type Pt (bishop or rook) placed on 's'.

pub fn attacks_bb(pt: PieceType, s: Square, occupied: Bitboard) -> Bitboard {
    match pt {
        BISHOP => {
            unsafe {
                let m = &BISHOP_MAGICS[s.0 as usize];
                m.attacks[m.index(occupied)]
            }
        }
        ROOK => {
            unsafe {
                let m = &ROOK_MAGICS[s.0 as usize];
                m.attacks[m.index(occupied)]
            }
        }
        QUEEN => {
            attacks_bb(BISHOP, s, occupied) | attacks_bb(ROOK, s, occupied)
        }
        _ => pseudo_attacks(pt, s)
    }
}
