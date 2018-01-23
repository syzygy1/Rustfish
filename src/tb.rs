// SPDX-License-Identifier: (GPL-3.0-or-later OR UPL-1.0)

use bitboard::*;
use movegen::*;
use position::Position;
use position::zobrist::material;
use search::RootMoves;
use types::*;
use ucioption;

use memmap::*;
use std;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};

static mut MAX_CARDINALITY: u32 = 0;
static mut MAX_CARDINALITY_DTM: u32 = 0;
static mut CARDINALITY: u32 = 0;
static mut CARDINALITY_DTM: u32 = 0;
static mut ROOT_IN_TB: bool = false;
static mut USE_RULE_50: bool = true;
static mut PROBE_DEPTH: Depth = Depth(0);

pub fn read_options() {
    unsafe {
        USE_RULE_50 = ucioption::get_bool("Syzygy50MoveRule");
        PROBE_DEPTH = ucioption::get_i32("SyzygyProbeDepth") * ONE_PLY;
        CARDINALITY = ucioption::get_i32("SyzygyProbeLimit") as u32;
        if CARDINALITY > MAX_CARDINALITY {
            CARDINALITY = MAX_CARDINALITY;
            PROBE_DEPTH = Depth::ZERO;
        }
        CARDINALITY_DTM = if ucioption::get_bool("SyzygyUseDTM") {
            std::cmp::min(CARDINALITY, MAX_CARDINALITY_DTM)
        } else {
            0
        };
    }
}

pub fn max_cardinality() -> u32 {
    unsafe { MAX_CARDINALITY }
}

pub fn cardinality() -> u32 {
    unsafe { CARDINALITY }
}

pub fn cardinality_dtm() -> u32 {
    unsafe { CARDINALITY_DTM }
}

pub fn root_in_tb() -> bool {
    unsafe { ROOT_IN_TB }
}

pub fn use_rule_50() -> bool {
    unsafe { USE_RULE_50 }
}

pub fn probe_depth() -> Depth {
    unsafe { PROBE_DEPTH }
}

const WDL_MAGIC: u32 = 0x5d23e871;
const DTM_MAGIC: u32 = 0x88ac504b;
const DTZ_MAGIC: u32 = 0xa50c66d7;

const WDL_SUFFIX: &str = ".rtbw";
const DTM_SUFFIX: &str = ".rtbm";
const DTZ_SUFFIX: &str = ".rtbz";

struct EncInfo {
    precomp: Option<Box<PairsData>>,
    factor: [u32; 6],
    pieces: [u8; 6],
    norm: [u8; 6],
}

impl EncInfo {
    pub fn new() -> EncInfo {
        EncInfo {
            precomp: None,
            factor: [0; 6],
            pieces: [0; 6],
            norm: [0; 6],
        }
    }
}

struct WdlPiece {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    ei: [EncInfo; 2],
    ready: AtomicBool,
}

struct DtmPiece {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    map: *const u16,
    ei: [EncInfo; 2],
    map_idx: [[u16; 2]; 2],
    ready: AtomicBool,
    loss_only: bool,
}

struct DtzPiece {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    map: *const u8,
    ei: EncInfo,
    map_idx: [u16; 4],
    ready: AtomicBool,
    flags: u8,
}

struct PieceEntry {
    key: Key,
    wdl: UnsafeCell<WdlPiece>,
    dtm: UnsafeCell<DtmPiece>,
    dtz: UnsafeCell<DtzPiece>,
    lock: Mutex<()>,
    num: u8,
    symmetric: bool,
    kk_enc: bool,
    has_dtm: bool,
    has_dtz: bool,
}

struct WdlPawn {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    ei: [[EncInfo; 2]; 4],
    ready: AtomicBool,
}

struct DtmPawn {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    map: *const u16,
    ei: [[EncInfo; 2]; 6],
    map_idx: [[[u16; 2]; 2]; 6],
    ready: AtomicBool,
    loss_only: bool,
    switched: bool,
}

struct DtzPawn {
    data: *const u8,
    mapping: Option<Box<Mmap>>,
    map: *const u8,
    ei: [EncInfo; 4],
    map_idx: [[u16; 4]; 4],
    flags: [u8; 4],
    ready: AtomicBool,
}

struct PawnEntry {
    key: Key,
    wdl: UnsafeCell<WdlPawn>,
    dtm: UnsafeCell<DtmPawn>,
    dtz: UnsafeCell<DtzPawn>,
    lock: Mutex<()>,
    num: u8,
    symmetric: bool,
    pawns: [u8; 2],
    has_dtm: bool,
    has_dtz: bool,
}

#[derive(Clone)]
enum TBEntry {
    Piece(usize),
    Pawn(usize),
}

// Given a position with 6 or fewer pieces, produce a text string
// of the form KQPvKRP, where "KQP" represents the white pieces if
// flip == false and the black pieces if flip == true.
fn prt_str(pos: &Position, flip: bool) -> String {
    let mut c = if flip { BLACK } else { WHITE };

    let mut s = String::new();

    for pt in (1..7).rev() {
        for _ in 0..pos.count(c, PieceType(pt)) {
            s.push(Position::PIECE_TO_CHAR.chars().nth(pt as usize).unwrap());
        }
    }
    s.push('v');
    c = !c;
    for pt in (1..7).rev() {
        for _ in 0..pos.count(c, PieceType(pt)) {
            s.push(Position::PIECE_TO_CHAR.chars().nth(pt as usize).unwrap());
        }
    }

    s
}

fn calc_key_from_pcs(pcs: &[i32; 16], flip: bool) -> Key {
    let mut key = Key(0);

    for c in 0..2 {
        for pt in 1..7 {
            let pc = Piece::make(Color(c), PieceType(pt));
            for i in 0..pcs[pc.0 as usize] {
                key ^= material(pc ^ flip, i);
            }
        }
    }

    key
}

fn calc_key_from_pieces(pieces: &[u8]) -> Key {
    let mut key = Key(0);

    let mut cnt = [0; 16];

    for &k in pieces.iter() {
        let pc = Piece(k as u32);
        key ^= material(pc, cnt[k as usize]);
        cnt[k as usize] += 1;
    }

    key
}

static mut PATH: Option<String> = None;

fn sep_char() -> char {
    if cfg!(target_os = "windows") { ';' } else { ':' }
}

fn test_tb(name: &str, suffix: &str) -> bool {
    let dirs = unsafe { PATH.as_ref().unwrap().split(sep_char()) };
    for dir in dirs {
        let file_name = format!("{}{}{}{}", dir, '/', name, suffix);
        let path = Path::new(&file_name);
        if path.is_file() {
            return true;
        }
    }

    false
}

fn open_tb(name: &str, suffix: &str) -> Option<fs::File> {
    let dirs = unsafe { PATH.as_ref().unwrap().split(sep_char()) };
    for dir in dirs {
        let file_name = format!("{}{}{}{}", dir, '/', name, suffix);
        if let Ok(file) = fs::File::open(file_name) {
            return Some(file);
        }
    }

    None
}

fn map_file(name: &str, suffix: &str) -> Option<Box<Mmap>> {
    let file = open_tb(name, suffix);
    if file.is_none() {
        return None;
    }

    let file = file.unwrap();
    match unsafe { MmapOptions::new().map(&file) } {
        Ok(mmap) => {
            Some(Box::new(mmap))
        }
        Err(err) => {
            eprintln!("{:?}", err.kind());
            None
        }
    }
}

struct GlobalVec<T> {
    v: *mut T,
    cap: usize,
    len: usize,
}

impl<T> GlobalVec<T> {
    pub fn init(&mut self, cap: usize) {
        self.save(Vec::with_capacity(cap));
    }

    fn save(&mut self, mut v: Vec<T>) {
        self.v = v.as_mut_ptr();
        self.len = v.len();
        self.cap = v.capacity();
        std::mem::forget(v);
    }

    fn get_vec(&self) -> Vec<T> {
        unsafe { Vec::from_raw_parts(self.v, self.len, self.cap) }
    }

    pub fn push(&mut self, item: T) {
        let mut v = self.get_vec();
        v.push(item);
        self.save(v);
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub unsafe fn reset(&mut self) {
        let mut v = self.get_vec();
        v.truncate(0);
        self.save(v);
    }

    pub unsafe fn free(&mut self) {
        std::mem::drop(self.get_vec());
    }
}

impl<T> std::ops::Index<usize> for GlobalVec<T> where T: 'static {
    type Output = T;

    fn index(&self, idx: usize) -> &'static T {
        unsafe {
            let elt_ref: &'static T = &*self.v.offset(idx as isize);
            elt_ref
        }
    }
}

static mut PIECE_ENTRIES: GlobalVec<PieceEntry> =
    GlobalVec { v: 0 as *mut PieceEntry, len: 0, cap: 0 };

static mut PAWN_ENTRIES: GlobalVec<PawnEntry> =
    GlobalVec { v: 0 as *mut PawnEntry, len: 0, cap: 0 };

static mut TB_MAP: *mut HashMap<Key, TBEntry> =
    0 as *mut HashMap<Key, TBEntry>;

static mut NUM_WDL: u32 = 0;
static mut NUM_DTM: u32 = 0;
static mut NUM_DTZ: u32 = 0;

pub fn init_tb(name: &str) {
    if !test_tb(&name, WDL_SUFFIX) {
        return;
    }

    let has_dtm = test_tb(&name, DTM_SUFFIX);
    let has_dtz = test_tb(&name, DTZ_SUFFIX);

    let mut pcs = [0; 16];
    let mut color = 0;
    for c in name.chars() {
        match c {
            'P' => pcs[PAWN.0 as usize   | color] += 1,
            'N' => pcs[KNIGHT.0 as usize | color] += 1,
            'B' => pcs[BISHOP.0 as usize | color] += 1,
            'R' => pcs[ROOK.0 as usize   | color] += 1,
            'Q' => pcs[QUEEN.0 as usize  | color] += 1,
            'K' => pcs[KING.0 as usize   | color] += 1,
            'v' => color = 8,
            _ => {}
        }
    }

    let key = calc_key_from_pcs(&pcs, false);
    let key2 = calc_key_from_pcs(&pcs, true);
    let symmetric = key == key2;

    let num = pcs.iter().sum::<i32>() as u32;
    unsafe {
        if num > MAX_CARDINALITY {
            MAX_CARDINALITY = num;
        }
        if has_dtm && num > MAX_CARDINALITY_DTM {
            MAX_CARDINALITY_DTM = num;
        }
    }

    let mut map = unsafe { Box::from_raw(TB_MAP) };

    let tb_entry;

    if pcs[W_PAWN.0 as usize] + pcs[B_PAWN.0 as usize] == 0 {
        let entry = PieceEntry {
            key: key,
            lock: Mutex::new(()),
            num: num as u8,
            symmetric: symmetric,
            kk_enc: pcs.iter().filter(|&n| *n == 1).count() == 2,
            has_dtm: has_dtm,
            has_dtz: has_dtz,
            wdl: UnsafeCell::new(WdlPiece {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                ei: [EncInfo::new(), EncInfo::new()],
            }),
            dtm: UnsafeCell::new(DtmPiece {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                ei: [EncInfo::new(), EncInfo::new()],
                map: std::ptr::null(),
                map_idx: [[0; 2]; 2],
                loss_only: false,
            }),
            dtz: UnsafeCell::new(DtzPiece {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                flags: 0,
                ei: EncInfo::new(),
                map: std::ptr::null(),
                map_idx: [0; 4],
            }),
        };
        unsafe { PIECE_ENTRIES.push(entry); }
        tb_entry = TBEntry::Piece(unsafe { PIECE_ENTRIES.len() - 1 });
    } else {
        let mut p0 = pcs[W_PAWN.0 as usize];
        let mut p1 = pcs[B_PAWN.0 as usize];
        if p1 > 0 && (p0 == 0 || p0 > p1) {
            std::mem::swap(&mut p0, &mut p1);
        }
        let entry = PawnEntry {
            key: key,
            lock: Mutex::new(()),
            num: num as u8,
            symmetric: symmetric,
            pawns: [p0 as u8, p1 as u8],
            has_dtm: has_dtm,
            has_dtz: has_dtz,
            wdl: UnsafeCell::new(WdlPawn {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                ei: [
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                ],
            }),
            dtm: UnsafeCell::new(DtmPawn {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                ei: [
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                    [EncInfo::new(), EncInfo::new()],
                ],
                map: std::ptr::null(),
                map_idx: [[[0; 2]; 2]; 6],
                loss_only: false,
                switched: false,
            }),
            dtz: UnsafeCell::new(DtzPawn {
                data: std::ptr::null(),
                mapping: None,
                ready: ATOMIC_BOOL_INIT,
                flags: [0; 4],
                ei: [
                    EncInfo::new(), EncInfo::new(),
                    EncInfo::new(), EncInfo::new()
                ],
                map: std::ptr::null(),
                map_idx: [[0; 4]; 4],
            }),
        };
        unsafe { PAWN_ENTRIES.push(entry); }
        tb_entry = TBEntry::Pawn(unsafe { PAWN_ENTRIES.len() - 1 });
    }

    map.insert(key, tb_entry.clone());
    if key != key2 {
        map.insert(key2, tb_entry);
    }

    unsafe {
        TB_MAP = Box::into_raw(map);
        NUM_WDL += 1;
        NUM_DTM += has_dtm as u32;
        NUM_DTZ += has_dtz as u32;
    }
}

pub fn free() {
    unsafe {
        std::mem::drop(Box::from_raw(TB_MAP));
        PIECE_ENTRIES.free();
        PAWN_ENTRIES.free();
    }
}

pub fn init(path: String) {
    const P: [char; 5] = [ 'Q', 'R', 'B', 'N', 'P' ];
    static mut INITIALIZED: bool = false;

    // Restrict engine to 5-piece TBs on platforms with 32-bit address space
    let max5 = std::mem::size_of::<usize>() < 8;

    unsafe {
        if !INITIALIZED {
            init_indices();
            PIECE_ENTRIES.init(if max5 { 84 } else { 254 });
            PAWN_ENTRIES.init(if max5 { 61 } else { 256 });
            TB_MAP = Box::into_raw(Box::new(HashMap::new()));
            INITIALIZED = true;
        }

        if PATH != None {
            PATH = None;
            std::mem::drop(Box::from_raw(TB_MAP));
            TB_MAP = Box::into_raw(Box::new(HashMap::new()));
            PIECE_ENTRIES.reset();
            PAWN_ENTRIES.reset();
            NUM_WDL = 0;
            NUM_DTM = 0;
            NUM_DTZ = 0;
            MAX_CARDINALITY = 0;
            MAX_CARDINALITY_DTM = 0;
        }
    }

    if path == "" || path == "<empty>" {
        return;
    }

    unsafe {
        PATH = Some(path);
    }

    for i in 0..5 {
        init_tb(&format!("K{}vK", P[i]));
    }

    for i in 0..5 {
        for j in i..5 {
            init_tb(&format!("K{}vK{}", P[i], P[j]));
        }
    }

    for i in 0..5 {
        for j in i..5 {
            init_tb(&format!("K{}{}vK", P[i], P[j]));
        }
    }

    for i in 0..5 {
        for j in i..5 {
            for k in 0..5 {
                init_tb(&format!("K{}{}vK{}", P[i], P[j], P[k]));
            }
        }
    }

    for i in 0..5 {
        for j in i..5 {
            for k in j..5 {
                init_tb(&format!("K{}{}{}vK", P[i], P[j], P[k]));
            }
        }
    }

    if !max5 {

        for i in 0..5 {
            for j in i..5 {
                for k in i..5 {
                    for l in (if i == k { j } else { k })..5 {
                        init_tb(&format!("K{}{}vK{}{}",
                            P[i], P[j], P[k], P[l]));
                    }
                }
            }
        }

        for i in 0..5 {
            for j in i..5 {
                for k in j..5 {
                    for l in 0..5 {
                        init_tb(&format!("K{}{}{}vK{}",
                            P[i], P[j], P[k], P[l]));
                    }
                }
            }
        }

        for i in 0..5 {
            for j in i..5 {
                for k in j..5 {
                    for l in k..5 {
                        init_tb(&format!("K{}{}{}{}vK",
                            P[i], P[j], P[k], P[l]));
                    }
                }
            }
        }

    }

    println!("info string Found {} WDL, {} DTM and {} DTZ tablebase files.",
        unsafe { NUM_WDL }, unsafe { NUM_DTM }, unsafe { NUM_DTZ });
}

// place k like pieces on n squares
fn subfactor(k: u32, n: u32) -> u32 {
    let mut f = n;
    let mut l = 1;
    for i in 1..k {
        f *= n - i;
        l *= i + 1;
    }

    f / l
}

fn calc_factors_piece(ei: &mut EncInfo, e: &PieceEntry, order: u8) -> usize {
    let mut i = ei.norm[0];
    let mut n = 64 - i;
    let mut f = 1;
    let mut k = 0;
    while i < e.num || k == order {
        if k == order {
            ei.factor[0] = f as u32;
            f *= if e.kk_enc { 462 } else { 31332 };
        } else {
            ei.factor[i as usize] = f as u32;
            f *= subfactor(ei.norm[i as usize] as u32, n as u32) as usize;
            n -= ei.norm[i as usize];
            i += ei.norm[i as usize];
        }
        k += 1;
    }

    f
}

fn calc_factors_pawn(
    ei: &mut EncInfo, e: &PawnEntry, order: u8, order2: u8, t: usize,
    by_file: bool
) -> usize {
    let mut i = ei.norm[0];
    if order2 < 0x0f {
        i += ei.norm[i as usize];
    }
    let mut n = 64 - i;
    let mut f = 1;
    let mut k = 0;
    while i < e.num || k == order || k == order2 {
        if k == order {
            ei.factor[0] = f as u32;
            f *= if by_file {
                pfactor(ei.norm[0] as usize - 1, t)
            } else {
                pfactor2(ei.norm[0] as usize - 1, t)
            }
        } else if k == order2 {
            ei.factor[ei.norm[0] as usize] = f as u32;
            f *= subfactor(ei.norm[ei.norm[0] as usize] as u32,
                48 - ei.norm[0] as u32) as usize;
        } else {
            ei.factor[i as usize] = f as u32;
            f *= subfactor(ei.norm[i as usize] as u32, n as u32) as usize;
            n -= ei.norm[i as usize];
            i += ei.norm[i as usize];
        }
        k += 1;
    }

    f
}

fn set_norm_piece(ei: &mut EncInfo, e: &PieceEntry) {
    ei.norm[0] = if e.kk_enc { 2 } else { 3 };

    let mut i = ei.norm[0] as usize;
    while i < e.num as usize {
        for j in i..e.num as usize {
            if ei.pieces[j] != ei.pieces[i] {
                break;
            }
            ei.norm[i] += 1;
        }
        i += ei.norm[i] as usize;
    }
}

fn set_norm_pawn(ei: &mut EncInfo, e: &PawnEntry) {
    ei.norm[0] = e.pawns[0];
    if e.pawns[1] > 0 {
        ei.norm[e.pawns[0] as usize] = e.pawns[1];
    }

    let mut i = (e.pawns[0] + e.pawns[1]) as usize;
    while i < e.num as usize {
        for j in i..e.num as usize {
            if ei.pieces[j] != ei.pieces[i] {
                break;
            }
            ei.norm[i] += 1;
        }
        i += ei.norm[i] as usize;
    }
}

fn setup_pieces_piece(
    ei: &mut EncInfo, e: &PieceEntry, data: *const u8, s: u32
) -> usize {
    let order;

    unsafe {
        for i in 0..(e.num as usize) {
            ei.pieces[i] = (*data.offset(i as isize + 1) >> s) & 0x0f;
        }
        order = (*data >> s) & 0x0f;
    }

    set_norm_piece(ei, e);
    calc_factors_piece(ei, e, order)
}

fn setup_pieces_pawn(
    ei: &mut EncInfo, e: &PawnEntry, data: *const u8, s: u32, t: usize,
    by_file: bool
) -> usize {
    let j = 1 + (e.pawns[1] > 0) as isize;
    let order;
    let order2;

    unsafe {
        for i in 0..(e.num as usize) {
            ei.pieces[i] = (*data.offset(i as isize + j) >> s) & 0x0f;
        }
        order = (*data >> s) & 0x0f;
        order2 =
            if e.pawns[1] > 0 { (*data.offset(1) >> s) & 0x0f } else { 0x0f };
    }

    set_norm_pawn(ei, e);
    calc_factors_pawn(ei, e, order, order2, t, by_file)
}

#[repr(packed)]
struct IndexEntry {
    block: u32,
    offset: u16,
}

struct PairsData {
    index_table: *const IndexEntry,
    size_table: *const u16,
    data: *const u8,
    offset: *const u16,
    sym_len: Vec<u8>,
    sym_pat: *const u8,
    block_size: u32,
    idx_bits: u32,
    min_len: u8,
    const_val: u16,
    base: Vec<u64>,
}

fn s1(w: *const u8) -> usize {
    unsafe {
        *w as usize | ((*w.offset(1) as usize & 0x0f) << 8)
    }
}

fn s2(w: *const u8) -> usize {
    unsafe {
        ((*w.offset(2) as usize) << 4) | (*w.offset(1) as usize >> 4)
    }
}

fn calc_sym_len(
    sym_len: &mut Vec<u8>, sym_pat: *const u8, s: usize, tmp: &mut Vec<u8>
) {
    if tmp[s] != 0 {
        return;
    }

    let w = unsafe { sym_pat.offset(3 * s as isize) };
    let s2 = s2(w);
    if s2 == 0x0fff {
        sym_len[s] = 0;
    } else {
        let s1 = s1(w);
        calc_sym_len(sym_len, sym_pat, s1, tmp);
        calc_sym_len(sym_len, sym_pat, s2, tmp);
        sym_len[s] = sym_len[s1] + sym_len[s2] + 1;
    }
    tmp[s] = 1;
}

fn setup_pairs(
    data: *const u8, tb_size: usize, size: &mut [isize],
    next: &mut *const u8, flags: &mut u8, is_wdl: bool
) -> Box<PairsData> {
    *flags = unsafe { *data };
    if *flags & 0x80 != 0 {
        *next = unsafe { data.offset(2) };
        return Box::new(PairsData {
            index_table: 0 as *const IndexEntry,
            size_table: 0 as *const u16,
            data: 0 as *const u8,
            offset: 0 as *const u16,
            sym_len: Vec::new(),
            sym_pat: 0 as *const u8,
            block_size: 0,
            idx_bits: 0,
            min_len: 0,
            const_val:
                if is_wdl { unsafe { *data.offset(1) as u16 } } else { 0 },
            base: Vec::new(),
        });
    }

    let block_size = unsafe { *data.offset(1) } as u32;
    let idx_bits = unsafe { *data.offset(2) } as u32;
    let real_num_blocks = u32::from_le(
        unsafe { *(data.offset(4) as *const u32) });
    let num_blocks = real_num_blocks + unsafe { *data.offset(3) } as u32;
    let max_len = unsafe { *data.offset(8) };
    let min_len = unsafe { *data.offset(9) };
    let h = (max_len - min_len + 1) as usize;
    let num_syms = u16::from_le(
        unsafe { *(data.offset(10 + 2 * h as isize) as *const u16) }) as usize;
    let mut sym_len = Vec::with_capacity(num_syms);
    for _ in 0..num_syms {
        sym_len.push(0u8);
    }
    let sym_pat = unsafe { data.offset(12 + 2 * h as isize) };

    let mut tmp = Vec::with_capacity(num_syms);
    for _ in 0..num_syms {
        tmp.push(0u8);
    }
    for s in 0..num_syms {
        calc_sym_len(&mut sym_len, sym_pat, s, &mut tmp);
    }

    let num_indices = (tb_size + (1usize << idx_bits) - 1) >> idx_bits;
    size[0] = 6 * num_indices as isize;
    size[1] = 2 * num_blocks as isize;
    size[2] = (real_num_blocks as isize) << block_size;

    *next = unsafe { data.offset(12 + 2 * h as isize + 3 * num_syms as isize
        + (num_syms & 1) as isize) };

    let offset = unsafe { data.offset(10) } as *const u16;
    let mut base = Vec::with_capacity(h);
    for _ in 0..h {
        base.push(0u64);
    }
    for i in (0..h-1).rev() {
        let b1 = unsafe { u16::from_le(*(offset.offset(i as isize))) } as u64;
        let b2 =
            unsafe { u16::from_le(*(offset.offset(1 + i as isize))) } as u64;
        base[i] = (base[i + 1] + b1 - b2) / 2;
    }
    for i in 0..h {
        base[i] <<= 64 - (min_len as usize + i);
    }

    Box::new(PairsData {
        index_table: 0 as *const IndexEntry,
        size_table: 0 as *const u16,
        data: 0 as *const u8,
        offset: unsafe { offset.offset(-(min_len as isize)) },
        sym_len: sym_len,
        sym_pat: sym_pat,
        block_size: block_size,
        idx_bits: idx_bits,
        min_len: min_len,
        const_val: 0,
        base: base,
    })
}

fn align_ptr(ptr: *const u8, align: usize) -> *const u8 {
    ((ptr as usize + align - 1) & !(align - 1)) as *const u8
}

fn init_table_piece_wdl(
    e: &PieceEntry, wdl: &mut WdlPiece, name: &str
) -> bool {
    let mmap = map_file(name, WDL_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    wdl.data = mmap.as_ptr();
    wdl.mapping = Some(mmap);

    let mut data = wdl.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != WDL_MAGIC {
        eprintln!("Corrupted table: {}{}", name, WDL_SUFFIX);
        wdl.mapping = None;
        wdl.data = 0 as *const u8;
        return false;
    }

    let split = unsafe { *data.offset(4) } & 0x01 != 0;
    data = unsafe { data.offset(5) };
    let tb_size_0 = setup_pieces_piece(&mut wdl.ei[0], e, data, 0);
    let tb_size_1 = setup_pieces_piece(&mut wdl.ei[1], e, data, 4);
    data = unsafe { data.offset(e.num as isize + 1) };
    data = align_ptr(data, 2);

    let mut size = [0isize; 6];
    let mut flags = 0u8;
    let mut next = 0 as *const u8;
    wdl.ei[0].precomp = Some(setup_pairs(data, tb_size_0, &mut size[0..3],
        &mut next, &mut flags, true));
    data = next;
    if split {
        wdl.ei[1].precomp = Some(setup_pairs(data, tb_size_1, &mut size[3..6],
            &mut next, &mut flags, true));
    }
    data = next;

    wdl.ei[0].precomp.as_mut().unwrap().index_table = data as *const IndexEntry;
    data = unsafe { data.offset(size[0]) };
    if split {
        wdl.ei[1].precomp.as_mut().unwrap().index_table =
            data as *const IndexEntry;
        data = unsafe { data.offset(size[3]) };
    }

    wdl.ei[0].precomp.as_mut().unwrap().size_table = data as *const u16;
    data = unsafe { data.offset(size[1]) };
    if split {
        wdl.ei[1].precomp.as_mut().unwrap().size_table = data as *const u16;
        data = unsafe { data.offset(size[4]) };
    }

    data = align_ptr(data, 64);
    wdl.ei[0].precomp.as_mut().unwrap().data = data;
    data = unsafe { data.offset(size[2]) };
    if split {
        data = align_ptr(data, 64);
        wdl.ei[1].precomp.as_mut().unwrap().data = data;
    }

    true
}

fn init_table_pawn_wdl(e: &PawnEntry, wdl: &mut WdlPawn, name: &str) -> bool {
    let mmap = map_file(name, WDL_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    wdl.data = mmap.as_ptr();
    wdl.mapping = Some(mmap);

    let mut data = wdl.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != WDL_MAGIC {
        eprintln!("Corrupted table: {}{}", name, WDL_SUFFIX);
        wdl.mapping = None;
        wdl.data = 0 as *const u8;
        return false;
    }

    let split = unsafe { *data.offset(4) } & 0x01 != 0;
    data = unsafe { data.offset(5) };

    let mut tb_size = [[0; 2]; 4];
    for f in 0..4 {
        tb_size[f][0] =
            setup_pieces_pawn(&mut wdl.ei[f][0], e, data, 0, f, true);
        tb_size[f][1] =
            setup_pieces_pawn(&mut wdl.ei[f][1], e, data, 4, f, true);
        data = unsafe {
            data.offset(e.num as isize + 1 + (e.pawns[1] > 0) as isize) };
    }
    data = align_ptr(data, 2);

    let mut size = [[0; 6]; 4];
    let mut next = 0 as *const u8;
    let mut flags = 0;
    for f in 0..4 {
        wdl.ei[f][0].precomp = Some(setup_pairs(data, tb_size[f][0],
            &mut size[f][0..3], &mut next, &mut flags, true));
        data = next;
        if split {
            wdl.ei[f][1].precomp = Some(setup_pairs(data, tb_size[f][1],
                &mut size[f][3..6], &mut next, &mut flags, true));
            data = next;
        }
    }

    for f in 0..4 {
        wdl.ei[f][0].precomp.as_mut().unwrap().index_table =
            data as *const IndexEntry;
        data = unsafe { data.offset(size[f][0]) };
        if split {
            wdl.ei[f][1].precomp.as_mut().unwrap().index_table =
                data as *const IndexEntry;
            data = unsafe { data.offset(size[f][3]) };
        }
    }

    for f in 0..4 {
        wdl.ei[f][0].precomp.as_mut().unwrap().size_table = data as *const u16;
        data = unsafe { data.offset(size[f][1]) };
        if split {
            wdl.ei[f][1].precomp.as_mut().unwrap().size_table =
                data as *const u16;
            data = unsafe { data.offset(size[f][4]) };
        }
    }

    for f in 0..4 {
        data = align_ptr(data, 64);
        wdl.ei[f][0].precomp.as_mut().unwrap().data = data;
        data = unsafe { data.offset(size[f][2]) };
        if split {
            data = align_ptr(data, 64);
            wdl.ei[f][1].precomp.as_mut().unwrap().data = data;
            data = unsafe { data.offset(size[f][5]) };
        }
    }

    true
}

fn init_table_piece_dtm(
    e: &PieceEntry, dtm: &mut DtmPiece, name: &str
) -> bool {
    let mmap = map_file(name, DTM_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    dtm.data = mmap.as_ptr();
    dtm.mapping = Some(mmap);

    let mut data = dtm.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != DTM_MAGIC {
        eprintln!("Corrupted table: {}{}", name, DTM_SUFFIX);
        dtm.mapping = None;
        dtm.data = 0 as *const u8;
        return false;
    }

    let split = unsafe { *data.offset(4) } & 0x01 != 0;
    dtm.loss_only = unsafe { *data.offset(4) } & 0x04 != 0;

    data = unsafe { data.offset(5) };
    let tb_size_0 = setup_pieces_piece(&mut dtm.ei[0], e, data, 0);
    let tb_size_1 = setup_pieces_piece(&mut dtm.ei[1], e, data, 4);
    data = unsafe { data.offset(e.num as isize + 1) };
    data = align_ptr(data, 2);

    let mut size = [0isize; 6];
    let mut flags = 0u8;
    let mut next = 0 as *const u8;
    dtm.ei[0].precomp = Some(setup_pairs(data, tb_size_0, &mut size[0..3],
        &mut next, &mut flags, true));
    data = next;
    if split {
        dtm.ei[1].precomp = Some(setup_pairs(data, tb_size_1, &mut size[3..6],
            &mut next, &mut flags, true));
    }
    data = next;

    if !dtm.loss_only {
        dtm.map = data as *const u16;
        let mut idx = 0;
        for i in 0..2 {
            dtm.map_idx[0][i] = 1 + idx;
            idx += 1 + u16::from_le(unsafe { *dtm.map.offset(idx as isize) });
        }
        if split {
            for i in 0..2 {
                dtm.map_idx[1][i] = 1 + idx;
                idx += 1
                    + u16::from_le(unsafe { *dtm.map.offset(idx as isize) });
            }
        }
        data = unsafe { dtm.map.offset(idx as isize) } as *const u8;
    }

    dtm.ei[0].precomp.as_mut().unwrap().index_table = data as *const IndexEntry;
    data = unsafe { data.offset(size[0]) };
    if split {
        dtm.ei[1].precomp.as_mut().unwrap().index_table =
            data as *const IndexEntry;
        data = unsafe { data.offset(size[3]) };
    }

    dtm.ei[0].precomp.as_mut().unwrap().size_table = data as *const u16;
    data = unsafe { data.offset(size[1]) };
    if split {
        dtm.ei[1].precomp.as_mut().unwrap().size_table = data as *const u16;
        data = unsafe { data.offset(size[4]) };
    }

    data = align_ptr(data, 64);
    dtm.ei[0].precomp.as_mut().unwrap().data = data;
    data = unsafe { data.offset(size[2]) };
    if split {
        data = align_ptr(data, 64);
        dtm.ei[1].precomp.as_mut().unwrap().data = data;
    }

    true
}

fn init_table_pawn_dtm(e: &PawnEntry, dtm: &mut DtmPawn, name: &str) -> bool {
    let mmap = map_file(name, DTM_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    dtm.data = mmap.as_ptr();
    dtm.mapping = Some(mmap);

    let mut data = dtm.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != DTM_MAGIC {
        eprintln!("Corrupted table: {}{}", name, DTM_SUFFIX);
        dtm.mapping = None;
        dtm.data = 0 as *const u8;
        return false;
    }

    let split = unsafe { *data.offset(4) } & 0x01 != 0;
    dtm.loss_only = unsafe { *data.offset(4) } & 0x04 != 0;
    data = unsafe { data.offset(5) };

    let mut tb_size = [[0; 2]; 6];
    for r in 0..6 {
        tb_size[r][0] =
            setup_pieces_pawn(&mut dtm.ei[r][0], e, data, 0, r, false);
        tb_size[r][1] =
            setup_pieces_pawn(&mut dtm.ei[r][1], e, data, 4, r, false);
        data = unsafe {
            data.offset(e.num as isize + 1 + (e.pawns[1] > 0) as isize) };
    }
    data = align_ptr(data, 2);

    let mut size = [[0; 6]; 6];
    let mut next = 0 as *const u8;
    let mut flags = 0;
    for r in 0..6 {
        dtm.ei[r][0].precomp = Some(setup_pairs(data, tb_size[r][0],
            &mut size[r][0..3], &mut next, &mut flags, true));
        data = next;
        if split {
            dtm.ei[r][1].precomp = Some(setup_pairs(data, tb_size[r][1],
                &mut size[r][3..6], &mut next, &mut flags, true));
            data = next;
        }
    }

    if !dtm.loss_only {
        dtm.map = data as *const u16;
        let mut idx = 0;
        for r in 0..6 {
            for i in 0..2 {
                dtm.map_idx[r][0][i] = 1 + idx;
                idx += 1
                    + u16::from_le(unsafe { *dtm.map.offset(idx as isize) });
            }
            if split {
                for i in 0..2 {
                    dtm.map_idx[r][1][i] = 1 + idx;
                    idx += 1 + u16::from_le(
                        unsafe { *dtm.map.offset(idx as isize) });
                }
            }
        }
        data = unsafe { dtm.map.offset(idx as isize) } as *const u8;
    }

    for r in 0..6 {
        dtm.ei[r][0].precomp.as_mut().unwrap().index_table =
            data as *const IndexEntry;
        data = unsafe { data.offset(size[r][0]) };
        if split {
            dtm.ei[r][1].precomp.as_mut().unwrap().index_table =
                data as *const IndexEntry;
            data = unsafe { data.offset(size[r][3]) };
        }
    }

    for r in 0..6 {
        dtm.ei[r][0].precomp.as_mut().unwrap().size_table = data as *const u16;
        data = unsafe { data.offset(size[r][1]) };
        if split {
            dtm.ei[r][1].precomp.as_mut().unwrap().size_table =
                data as *const u16;
            data = unsafe { data.offset(size[r][4]) };
        }
    }

    for r in 0..6 {
        data = align_ptr(data, 64);
        dtm.ei[r][0].precomp.as_mut().unwrap().data = data;
        data = unsafe { data.offset(size[r][2]) };
        if split {
            data = align_ptr(data, 64);
            dtm.ei[r][1].precomp.as_mut().unwrap().data = data;
            data = unsafe { data.offset(size[r][5]) };
        }
    }

    if calc_key_from_pieces(&dtm.ei[0][0].pieces[0..e.num as usize]) != e.key {
        dtm.switched = true;
    }

    true
}

fn init_table_piece_dtz(
    e: &PieceEntry, dtz: &mut DtzPiece, name: &str
) -> bool {
    let mmap = map_file(name, DTZ_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    dtz.data = mmap.as_ptr();
    dtz.mapping = Some(mmap);

    let mut data = dtz.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != DTZ_MAGIC {
        eprintln!("Corrupted table: {}{}", name, DTZ_SUFFIX);
        dtz.mapping = None;
        dtz.data = 0 as *const u8;
        return false;
    }

    data = unsafe { data.offset(5) };
    let tb_size = setup_pieces_piece(&mut dtz.ei, e, data, 0);
    data = unsafe { data.offset(e.num as isize + 1) };
    data = align_ptr(data, 2);

    let mut size = [0isize; 3];
    let mut flags = 0u8;
    let mut next = 0 as *const u8;
    dtz.ei.precomp = Some(setup_pairs(data, tb_size, &mut size, &mut next,
        &mut flags, true));
    dtz.flags = flags;
    data = next;

    if dtz.flags & 2 != 0 {
        dtz.map = data;
        let mut idx = 0;
        for i in 0..4 {
            dtz.map_idx[i] = 1 + idx;
            idx += 1 + unsafe { *data.offset(idx as isize) } as u16;
        }
        data = unsafe { data.offset(idx as isize) };
        data = align_ptr(data, 2);
    }

    dtz.ei.precomp.as_mut().unwrap().index_table = data as *const IndexEntry;
    data = unsafe { data.offset(size[0]) };

    dtz.ei.precomp.as_mut().unwrap().size_table = data as *const u16;
    data = unsafe { data.offset(size[1]) };

    data = align_ptr(data, 64);
    dtz.ei.precomp.as_mut().unwrap().data = data;

    true
}

fn init_table_pawn_dtz(
    e: &PawnEntry, dtz: &mut DtzPawn, name: &str
) -> bool {
    let mmap = map_file(name, DTZ_SUFFIX);
    if mmap.is_none() {
        return false;
    }
    let mmap = mmap.unwrap();

    dtz.data = mmap.as_ptr();
    dtz.mapping = Some(mmap);

    let mut data = dtz.data;

    if u32::from_le(unsafe { *(data as *const u32) }) != DTZ_MAGIC {
        eprintln!("Corrupted table: {}{}", name, DTZ_SUFFIX);
        dtz.mapping = None;
        dtz.data = 0 as *const u8;
        return false;
    }

    data = unsafe { data.offset(5) };

    let mut tb_size = [0; 4];
    for f in 0..4 {
        tb_size[f] = setup_pieces_pawn(&mut dtz.ei[f], e, data, 0, f, true);
        data = unsafe {
            data.offset(e.num as isize + 1 + (e.pawns[1] > 0) as isize) };
    }
    data = align_ptr(data, 2);

    let mut size = [[0; 3]; 4];
    let mut flags = 0u8;
    let mut next = 0 as *const u8;
    for f in 0..4 {
        dtz.ei[f].precomp = Some(setup_pairs(data, tb_size[f], &mut size[f],
            &mut next, &mut flags, true));
        dtz.flags[f] = flags;
        data = next;
    }

    dtz.map = data;
    let mut idx = 0;
    for f in 0..4 {
        if dtz.flags[f] & 2 != 0 {
            for i in 0..4 {
                dtz.map_idx[f][i] = 1 + idx;
                idx += 1 + unsafe { *data.offset(idx as isize) } as u16;
            }
        }
    }
    data = unsafe { data.offset(idx as isize) };
    data = align_ptr(data, 2);

    for f in 0..4 {
        dtz.ei[f].precomp.as_mut().unwrap().index_table =
            data as *const IndexEntry;
        data = unsafe { data.offset(size[f][0]) };
    }

    for f in 0..4 {
        dtz.ei[f].precomp.as_mut().unwrap().size_table = data as *const u16;
        data = unsafe { data.offset(size[f][1]) };
    }

    for f in 0..4 {
        data = align_ptr(data, 64);
        dtz.ei[f].precomp.as_mut().unwrap().data = data;
        data = unsafe { data.offset(size[f][2]) };
    }

    true
}

fn fill_squares(
    pos: &Position, pc: &[u8; 6], num: usize, flip: bool, p: &mut [Square; 6]
) {
    let mut i = 0;
    loop {
        let piece = Piece(pc[i] as u32);
        let b = pos.pieces_cp(piece.color() ^ flip, piece.piece_type());
        for sq in b {
            p[i] = sq;
            i += 1;
        }
        if i == num as usize {
            break;
        }
    }
}

fn probe_wdl_table(pos: &Position, success: &mut i32) -> i32 {
    // Obtain the position's material signature key
    let key = pos.material_key();

    // Test for KvK
    if pos.pieces() == pos.pieces_p(KING) {
        return 0;
    }

    let mut p: [Square; 6] = [Square(0); 6];
    let mut res = 0;
    let map = unsafe { Box::from_raw(TB_MAP) };

    loop { match map.get(&key) {
        None => {
            *success = 0;
        }
        Some(&TBEntry::Piece(idx)) => {
            let e = unsafe { &PIECE_ENTRIES[idx] };
            let wdl = unsafe { &*e.wdl.get() };
            if !wdl.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !wdl.ready.load(Ordering::Relaxed) {
                    if !init_table_piece_wdl(e, unsafe { &mut *e.wdl.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // somehow disable the table?
                        *success = 0;
                        break;
                    }
                    wdl.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { key != e.key }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && (key != e.key) == (pos.side_to_move() == WHITE)) as usize;

            fill_squares(pos, &wdl.ei[bside].pieces, e.num as usize,
                flip, &mut p);
            let idx = encode_piece(&mut p, &wdl.ei[bside], &e);

            res = decompress_pairs(
                &(wdl.ei[bside].precomp.as_ref().unwrap()), idx);
        }
        Some(&TBEntry::Pawn(idx)) => {
            let e = unsafe { &PAWN_ENTRIES[idx] };
            let wdl = unsafe { &*e.wdl.get() };
            if !wdl.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !wdl.ready.load(Ordering::Relaxed) {
                    if !init_table_pawn_wdl(e, unsafe { &mut *e.wdl.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // somehow disable the table?
                        *success = 0;
                        break;
                    }
                    wdl.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { key != e.key }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && (key != e.key) == (pos.side_to_move() == WHITE)) as usize;

            let color = Piece(wdl.ei[0][0].pieces[0] as u32).color();
            let b = pos.pieces_cp(color ^ flip, PAWN);
            let f = leading_pawn_file(b) as usize;
            fill_squares(pos, &wdl.ei[f][bside].pieces, e.num as usize, flip,
                &mut p);
            if flip {
                for i in 0..e.num as usize {
                    p[i] = !p[i];
                }
            }
            let idx = encode_pawn(&mut p, &wdl.ei[f][bside], &e);

            res = decompress_pairs(
                &wdl.ei[f][bside].precomp.as_ref().unwrap(), idx);
        }
    } break; }

    std::mem::forget(map);

    (res as i32) - 2
}

fn probe_dtm_table(pos: &Position, won: bool, success: &mut i32) -> i32 {
    // Obtain the position's material signature key
    let key = pos.material_key();

    let mut p: [Square; 6] = [Square(0); 6];
    let mut res = 0;
    let map = unsafe { Box::from_raw(TB_MAP) };

    loop { match map.get(&key) {
        None => {
            *success = 0;
        }
        Some(&TBEntry::Piece(idx)) => {
            let e = unsafe { &PIECE_ENTRIES[idx] };
            if !e.has_dtm {
                *success = 0;
                break;
            }

            let dtm = unsafe { &*e.dtm.get() };
            if !dtm.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !dtm.ready.load(Ordering::Relaxed) {
                    if !init_table_piece_dtm(e, unsafe { &mut *e.dtm.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // e.has_dtm = false;
                        *success = 0;
                        break;
                    }
                    dtm.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { key != e.key }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && (key != e.key) == (pos.side_to_move() == WHITE)) as usize;

            fill_squares(pos, &dtm.ei[bside as usize].pieces, e.num as usize,
                flip, &mut p);
            let idx = encode_piece(&mut p, &dtm.ei[bside], &e);

            res = decompress_pairs(
                &dtm.ei[bside].precomp.as_ref().unwrap(), idx);
            if !dtm.loss_only {
                res = unsafe {
                    u16::from_le(*dtm.map.offset(u16::from_le(dtm.map_idx
                    [bside][won as usize]) as isize + res as isize)) as u32
                };
            }
        }
        Some(&TBEntry::Pawn(idx)) => {
            let e = unsafe { &PAWN_ENTRIES[idx] };
            if !e.has_dtm {
                *success = 0;
                break;
            }

            let dtm = unsafe { &*e.dtm.get() };
            if !dtm.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !dtm.ready.load(Ordering::Relaxed) {
                    if !init_table_pawn_dtm(e, unsafe { &mut *e.dtm.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // e.has_dtm = false;
                        *success = 0;
                        break;
                    }
                    dtm.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { (key != e.key) != dtm.switched }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && ((key != e.key) != dtm.switched) ==
                    (pos.side_to_move() == WHITE)) as usize;

            let color = Piece(dtm.ei[0][0].pieces[0] as u32).color();
            let b = pos.pieces_cp(color ^ flip, PAWN);
            let r = leading_pawn_rank(b, flip) as usize;
            fill_squares(pos, &dtm.ei[r][bside].pieces, e.num as usize, flip,
                &mut p);
            if flip {
                for i in 0..e.num as usize {
                    p[i] = !p[i];
                }
            }
            let idx = encode_pawn2(&mut p, &dtm.ei[r][bside], &e);

            res = decompress_pairs(
                &dtm.ei[r][bside].precomp.as_ref().unwrap(), idx);
            if !dtm.loss_only {
                res = unsafe {
                    u16::from_le(*dtm.map.offset(u16::from_le(dtm.map_idx[r]
                    [bside][won as usize]) as isize + res as isize)) as u32
                };
            }
        }
    } break; }

    std::mem::forget(map);

    res as i32
}

fn probe_dtz_table(pos: &Position, wdl: i32, success: &mut i32) -> i32 {
    const WDL_TO_MAP: [u32; 5] = [1, 3, 0, 2, 0];
    const PA_FLAGS: [u8; 5] = [ 8, 0, 0, 0, 4 ];

    // Obtain the position's material signature key
    let key = pos.material_key();

    let mut p: [Square; 6] = [Square(0); 6];
    let mut res = 0;
    let map = unsafe { Box::from_raw(TB_MAP) };

    loop { match map.get(&key) {
        None => {
            *success = 0;
        }
        Some(&TBEntry::Piece(idx)) => {
            let e = unsafe { &PIECE_ENTRIES[idx] };
            if !e.has_dtz {
                *success = 0;
                break;
            }

            let dtz = unsafe { &*e.dtz.get() };
            if !dtz.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !dtz.ready.load(Ordering::Relaxed) {
                    if !init_table_piece_dtz(e, unsafe { &mut *e.dtz.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // e.has_dtz = false;
                        *success = 0;
                        break;
                    }
                    dtz.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { key != e.key }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && (key != e.key) == (pos.side_to_move() == WHITE)) as usize;

            if (dtz.flags & 1) as usize != bside
                && !e.symmetric
            {
                *success = -1;
                break;
            }

            fill_squares(pos, &dtz.ei.pieces, e.num as usize,
                flip, &mut p);
            let idx = encode_piece(&mut p, &dtz.ei, &e);

            res = decompress_pairs(
                &dtz.ei.precomp.as_ref().unwrap(), idx) as i32;
            if dtz.flags & 2 != 0 {
                res = unsafe { *dtz.map.offset(dtz.map_idx[WDL_TO_MAP[(wdl + 2) as usize] as usize] as isize + res as isize) } as i32;
            }
            if dtz.flags & PA_FLAGS[(wdl + 2) as usize] == 0 || wdl & 1 != 0 {
                res *= 2;
            }
        }
        Some(&TBEntry::Pawn(idx)) => {
            let e = unsafe { &PAWN_ENTRIES[idx] };
            if !e.has_dtz {
                *success = 0;
                break;
            }

            let dtz = unsafe { &*e.dtz.get() };
            if !dtz.ready.load(Ordering::Acquire) {
                let _lock = e.lock.lock().unwrap();
                if !dtz.ready.load(Ordering::Relaxed) {
                    if !init_table_pawn_dtz(e, unsafe { &mut *e.dtz.get() },
                        &prt_str(pos, e.key != key))
                    {
                        // e.has_dtz = false;
                        *success = 0;
                        break;
                    }
                    dtz.ready.store(true, Ordering::Release);
                }
            }

            let flip =
                if !e.symmetric { key != e.key }
                else { pos.side_to_move() != WHITE };
            let bside = (!e.symmetric
                && (key != e.key) == (pos.side_to_move() == WHITE)) as usize;

            let color = Piece(dtz.ei[0].pieces[0] as u32).color();
            let b = pos.pieces_cp(color ^ flip, PAWN);
            let f = leading_pawn_file(b) as usize;

            if (dtz.flags[f] & 1) as usize != bside
                && !e.symmetric
            {
                *success = -1;
                break;
            }

            fill_squares(pos, &dtz.ei[f].pieces, e.num as usize, flip,
                &mut p);
            if flip {
                for i in 0..e.num as usize {
                    p[i] = !p[i];
                }
            }
            let idx = encode_pawn(&mut p, &dtz.ei[f], &e);

            res = decompress_pairs(
                &dtz.ei[f].precomp.as_ref().unwrap(), idx) as i32;
            if dtz.flags[f] & 2 != 0 {
                res = unsafe {
                    *dtz.map.offset(dtz.map_idx[f][WDL_TO_MAP[(wdl + 2)
                    as usize] as usize] as isize + res as isize)
                } as i32;
            }
            if dtz.flags[f] & PA_FLAGS[(wdl + 2) as usize] == 0
                || wdl & 1 != 0
            {
                res *= 2;
            }
        }
    } break; }

    std::mem::forget(map);

    res
}

// Add underpromotion captures to list of captures.
fn add_underprom_caps(
    pos: &Position, list: &mut [ExtMove], end: usize
) -> usize {
    let mut extra = end;

    for idx in 0..end {
        let m = list[idx].m;
        if m.move_type() == PROMOTION && pos.piece_on(m.to()) != NO_PIECE {
            list[extra    ].m = Move(m.0 - (1 << 12));
            list[extra + 1].m = Move(m.0 - (2 << 12));
            list[extra + 2].m = Move(m.0 - (3 << 12));
            extra += 3;
        }
    }

    extra
}

fn probe_ab(pos: &mut Position, mut alpha: i32, beta: i32, success: &mut i32) -> i32 {
    assert!(pos.ep_square() == Square::NONE);

    let mut list: [ExtMove; 64] = [ExtMove { m: Move::NONE, value: 0 }; 64];

    let end = if pos.checkers() == 0 {
        let end = generate_captures(pos, &mut list, 0);
        add_underprom_caps(pos, &mut list, end)
    } else {
        generate_evasions(pos, &mut list, 0)
    };

    for &m in list[0..end].iter() {
        if !pos.capture(m.m) || !pos.legal(m.m) {
            continue;
        }
        let gives_check = pos.gives_check(m.m);
        pos.do_move(m.m, gives_check);
        let v = -probe_ab(pos, -beta, -alpha, success);
        pos.undo_move(m.m);
        if *success == 0 {
            return 0;
        }
        if v > alpha {
            if v >= beta {
                return v;
            }
            alpha = v;
        }
    }

    let v = probe_wdl_table(pos, success);

    if alpha >= v { alpha } else { v }
}

// Probe the WDL table for a particular position.
//
// If *success != 0, the probe was successful.
//
// If *success == 2, the position has a winning capture, or the position
// is a cursed win and has a cursed winning capture, or the positoin has
// en ep captures as only best move.
// This information is used in probe_dtz().
//
// The return value is from the point of view of the side to move.
// -2 : loss
// -1 : loss, but draw under the 50-move rule
//  0 : draw
//  1 : win, but draw under the 50-move rule
//  2 : win
pub fn probe_wdl(pos: &mut Position, success: &mut i32) -> i32 {
    // Generate (at least) all legal en-passant captures
    let mut list: [ExtMove; 64] = [ExtMove { m: Move::NONE, value: 0 }; 64];

    let mut end = if pos.checkers() == 0 {
        let end = generate_captures(pos, &mut list, 0);
        add_underprom_caps(pos, &mut list, end)
    } else {
        generate_evasions(pos, &mut list, 0)
    };

    let mut best_cap = -3;
    let mut best_ep = -3;

    for &m in list[0..end].iter() {
        if !pos.capture(m.m) || !pos.legal(m.m) {
            continue;
        }
        let gives_check = pos.gives_check(m.m);
        pos.do_move(m.m, gives_check);
        let v = -probe_ab(pos, -2, -best_cap, success);
        pos.undo_move(m.m);
        if *success == 0 {
            return 0;
        }
        if v > best_cap {
            if v == 2 {
                *success = 2;
                return 2;
            }
            if m.m.move_type() != ENPASSANT {
                best_cap = v;
            } else if v > best_ep {
                best_ep = v;
            }
        }
    }

    let v = probe_wdl_table(pos, success);
    if *success == 0 {
        return 0;
    }

    // Now max(v, best_cap) is the WDL value of the position wihtout
    // ep rights. If the position without ep rights is not stalemate or
    // no ep captures exist, then the value of the position is
    // max(v, best_cap, best_ep). If the position without ep rights is
    // stalemate and best_ep > -3, then the value of the position is
    // best_ep (and we will have v == 0).

    if best_ep > best_cap {
        if best_ep > v {
            // ep capture (possibly cursed losing) is best
            *success = 2;
            return best_ep;
        }
        best_cap = best_ep;
    }

    // Now max(v, best_cap) is the WDL value of the position, unless the
    // position without ep rights is stalemate and best_ep > -3.

    if best_cap >= v {
        // No need to test for the stalemate case here: either there are
        // non-ep captures, or best_cap == best_ep >= v anyway.
        *success = 1 + (best_cap > 0) as i32;
        return best_cap;
    }

    // Now handle the stalemate case.
    if best_ep > -3 && v == 0 {
        // Check for stalemate in the position without ep captures.
        for &m in list[0..end].iter() {
            if m.m.move_type() != ENPASSANT && pos.legal(m.m) {
                return v;
            }
        }
        if pos.checkers() == 0 {
            end = generate_quiets(pos, &mut list, 0);
            for &m in list[0..end].iter() {
                if m.m.move_type() != ENPASSANT && pos.legal(m.m) {
                    return v;
                }
            }
        }
        *success = 2;
        return best_ep;
    }

    v
}

// Probe a position known to lose by probing the DTM table and looking
// at captures.
fn probe_dtm_loss(pos: &mut Position, success: &mut i32) -> Value {
    let mut best = -Value::INFINITE;
    let mut num_ep = 0;

    // Generate at least all legal captures including (under)promotions
    let mut list: [ExtMove; 64] = [ExtMove { m: Move::NONE, value: 0 }; 64];
    let end = if pos.checkers() == 0 {
        let end = generate_captures(pos, &mut list, 0);
        add_underprom_caps(pos, &mut list, end)
    } else {
        generate_evasions(pos, &mut list, 0)
    };

    for &m in list[0..end].iter() {
        if !pos.capture(m.m) || !pos.legal(m.m) {
            continue;
        }
        if m.m.move_type() == ENPASSANT {
            num_ep += 1;
        }

        let gives_check = pos.gives_check(m.m);
        pos.do_move(m.m, gives_check);

        let v = -probe_dtm_win(pos, success) + 1;

        pos.undo_move(m.m);

        best = std::cmp::max(best, v);
        if *success == 0 {
            return Value::NONE;
        }
    }

    // If there are en-passant captures, the position without ep rights
    // may be a stalemate. If it is, we must avoid probing the DTM table.
    if num_ep != 0 && MoveList::new(pos, GenType::Legal).size() == num_ep {
        return best;
    }

    let v = -Value::MATE + 2 * probe_dtm_table(pos, false, success);
    std::cmp::max(best, v)
}

fn probe_dtm_win(pos: &mut Position, success: &mut i32) -> Value {
    let mut best = -Value::INFINITE;

    // Generate all moves
    let mut list: [ExtMove; 256] = [ExtMove { m: Move::NONE, value: 0 }; 256];
    let end = if pos.checkers() != 0 {
        generate_evasions(pos, &mut list, 0)
    } else {
        generate_non_evasions(pos, &mut list, 0)
    };

    // Perform a 1-ply search
    for &m in list[0..end].iter() {
        if !pos.legal(m.m) {
            continue;
        }

        let gives_check = pos.gives_check(m.m);
        pos.do_move(m.m, gives_check);

        let wdl = if pos.ep_square() != Square::NONE {
            probe_wdl(pos, success)
        } else {
            probe_ab(pos, -1, 0, success)
        };
        let v = if wdl < 0 && *success != 0 {
            -probe_dtm_loss(pos, success) - 1
        } else {
            -Value::INFINITE
        };

        pos.undo_move(m.m);

        best = std::cmp::max(best, v);
        if *success == 0 {
            return Value::NONE;
        }
    }

    best
}

pub fn probe_dtm(pos: &mut Position, wdl: i32, success: &mut i32) -> Value {
    debug_assert!(wdl != 0);

    if wdl > 0 {
        probe_dtm_win(pos, success)
    } else {
        probe_dtm_loss(pos, success)
    }
}

const WDL_TO_DTZ: [i32; 5] = [ -1, -101, 0, 101, 1 ];

// Probe the DTZ table for a particular position.
// If *success != 0, the probe was successful.
// The return value is from the point of view of the side to move:
//         n < -100 : loss, but draw under 50-move rule
// -100 <= n < -1   : loss in n ply (assuming 50-move counter == 0)
//         0        : draw
//     1 < n <= 100 : win in n ply (assuming 50-move counter == 0)
//   100 < n        : win, but draw under 50-move rule
//
// If the position mate, -1 is returned instead of 0.
//
// The return value n can be off by 1: a return value -n can mean a loss
// in n+1 ply and a return value +n can mean a win in n+1 ply. This
// cannot happen for tables with positions exactly on the "edge" of
// the 50-move rule.
//
// This means that if dtz > 0 is returned, the position is certainly
// a win if dtz + 50-move-counter <= 99. Care must be taken that the engine
// picks moves that preserve dtz + 50-move-counter <= 99.
//
// If n = 100 immediately after a capture or pawn move, then the position
// is also certainly a win, and during the whole phase until the next
// capture or pawn move, the inequality to be preserved is
// dtz + 50-movecounter <= 100.
//
// In short, if a move is available resulting in dtz + 50-move-counter <= 99,
// then do not accept moves leading to dtz + 50-move-counter == 100.
//
pub fn probe_dtz(pos: &mut Position, success: &mut i32) -> i32 {
    let wdl = probe_wdl(pos, success);
    if *success == 0 {
        return 0;
    }

    // If draw, then dtz = 0
    if wdl == 0 {
        return 0;
    }

    // Check for winning capture or en-passant capture as only best move
    if *success == 2 {
        return WDL_TO_DTZ[(wdl + 2) as usize];
    }

    let mut list: [ExtMove; 256] = [ExtMove { m: Move::NONE, value: 0 }; 256];
    let mut end = 0;

    // If winning, check for a winning pawn move.
    if wdl > 0 {
        end = if pos.checkers() == 0 {
            generate_non_evasions(pos, &mut list, 0)
        } else {
            generate_evasions(pos, &mut list, 0)
        };

        for &m in list[0..end].iter() {
            if pos.moved_piece(m.m).piece_type() != PAWN
                || pos.capture(m.m)
                || !pos.legal(m.m)
            {
                continue;
            }
            let gives_check = pos.gives_check(m.m);
            pos.do_move(m.m, gives_check);
            let v = -probe_wdl(pos, success);
            pos.undo_move(m.m);
            if *success == 0 {
                return 0;
            }
            if v == wdl {
                return WDL_TO_DTZ[(wdl + 2) as usize];
            }
        }
    }

    // If we are here, we know that the best move is not an ep capture.
    // In other words, the value of wdl corresponds to the WDL value of
    // the position without ep rights. It is therefore safe to probe the
    // DTZ table with the current value of wdl.

    let dtz = probe_dtz_table(pos, wdl, success);
    if *success >= 0 {
        return
            WDL_TO_DTZ[(wdl + 2) as usize] + if wdl > 0 { dtz } else { -dtz };
    }

    // *success < 0 means we need to probe DTZ for the other side to move
    let mut best;
    if wdl > 0 {
        best = std::i32::MAX;
        // If wdl > 0, we have already generated all moves
    } else {
        // If (cursed) loss, the worst case is a losing capture or pawn
        // move as the "best" move, leading to dtz of -1 or -10.
        // In case of mate, this will cause -1 to be returned.
        best = WDL_TO_DTZ[(wdl + 2) as usize];
        // If wdl < 0, we still have to generate all moves
        end = if pos.checkers() == 0 {
            generate_non_evasions(pos, &mut list, 0)
        } else {
            generate_evasions(pos, &mut list, 0)
        };
    }

    for &m in list[..end].iter() {
        // We can skip pawn moves and captures.
        // If wdl > 0, we already caught them. If wdl < 0, the initial
        // value of best already takes account of them.
        if pos.capture(m.m)
            || pos.moved_piece(m.m).piece_type() == PAWN
            || !pos.legal(m.m)
        {
            continue;
        }
        let gives_check = pos.gives_check(m.m);
        pos.do_move(m.m, gives_check);
        let v = -probe_dtz(pos, success);
        pos.undo_move(m.m);
        if *success == 0 {
            return 0;
        }
        if wdl > 0 {
            if v > 0 && v + 1 < best {
                best = v + 1;
            }
        } else {
            if v - 1 < best {
                best = v - 1;
            }
        }
    }

    best
}

// Use the DTZ tables to rank and score all root moves in the list.
// A return value of false means that not all probes were successful.
fn root_probe_dtz(pos: &mut Position, root_moves: &mut RootMoves) -> bool {
    let mut success = 1;

    // Obtain 50-move counter for the root position
    let cnt50 = pos.rule50_count();

    // Check whether a position was repeated since the last zeroing move.
    // In that case, we need to be careful and play DTZ-optimal moves if
    // winning.
    let rep = pos.has_repeated();

    // The border between draw and win lies at rank 1 or rank 900, depending
    // on whether the 50-move rule is used
    let bound = if ucioption::get_bool("Syzygy50MoveRule") { 900 } else { 1 };

    // Probe, rank and score each move
    for ref mut rm in root_moves.iter_mut() {
        let m = rm.pv[0];
        let gives_check = pos.gives_check(m);
        pos.do_move(m, gives_check);

        // Calculate dtz for the current move, counting from the root position
        let mut v;
        if pos.rule50_count() == 0 {
            // If the move resets the 50-move counter, dtz is -10/-1/0/1/101
            v = -probe_wdl(pos, &mut success);
            v = WDL_TO_DTZ[(v + 2) as usize];
        } else {
            // Otherwise, take dtz for the new position and correct by 1 ply
            v = -probe_dtz(pos, &mut success);
            if v > 0 {
                v += 1;
            } else if v < 0 {
                v -= 1;
            }
        }
        // Make sure that a mating move gets value 1
        if pos.checkers() != 0
            && v == 2
            && MoveList::new(pos, GenType::Legal).size() == 0
        {
            v = 1;
        }

        pos.undo_move(m);
        if success == 0 {
            return false;
        }

        // Better moves are ranked higher. Guaranteed wins are ranked
        // equally. Losing moves are ranked equally unless a 50-move draw
        // is in sight. Note that moves ranked 900 have dtz + cnt50 == 100,
        // which in rare cases may be insufficient to win as dtz may be
        // off by one (see the comments before probe_dtz()).
        let r =
            if v > 0 {
                if v + cnt50 <= 99 && !rep { 1000 } else { 1000 - (v + cnt50) }
            } else if v < 0 {
                if -v * 2 + cnt50 < 100 { -1000 } else { -1000 + (-v + cnt50) }
            } else { 0 };
        rm.tb_rank = r;

        // Determine the score to be displayed for this move. Assign at
        // least 1 cp to cursed wins and let it grow to 49 cp as the position
        // gets closer to a real win.
        rm.tb_score =
            if r >= bound { Value::MATE - MAX_MATE_PLY - 1 }
            else if r > 0 { std::cmp::max(3, r - 800) * PawnValueEg / 200 }
            else if r == 0 { Value::DRAW }
            else if r > -bound { std::cmp::max(-3, r+800) * PawnValueEg / 200 }
            else { -Value::MATE + MAX_MATE_PLY + 1 };
    }

    true
}

// Use the WDL tables to rank all root moves in the list.
// This is a fallback for the case that some or all DTZ tables are missing.
// A return value of false means that not all probes were successful.
fn root_probe_wdl(pos: &mut Position, root_moves: &mut RootMoves) -> bool {
    const WDL_TO_RANK: [i32; 5] = [ -1000, -899, 0, 899, 1000 ];
    const WDL_TO_VALUE: [Value; 5] = [
        Value(-32000 + 128 + 1), Value(-2), Value(0), Value(2),
        Value(32000 - 128 - 1)
//        -Value::MATE + MAX_MATE_PLY + 1, Value::DRAW - 2, Value::DRAW,
//        Value::DRAW + 2, Value::MATE - MAX_MATE_PLY - 1,
    ];

    let mut success = 1;
    let move50 = ucioption::get_bool("Syzygy50MoveRule");

    // Probe, rank and score each move
    for ref mut rm in root_moves.iter_mut() {
        let m = rm.pv[0];
        let gives_check = pos.gives_check(m);
        pos.do_move(m, gives_check);

        let mut v = -probe_wdl(pos, &mut success);

        pos.undo_move(m);

        if success == 0 {
            return false;
        }
        if !move50 {
            v = if v > 0 { 2 } else if v < 0 { -2 } else { 0 };
        }
        rm.tb_rank = WDL_TO_RANK[(v + 2) as usize];
        rm.tb_score = WDL_TO_VALUE[(v + 2) as usize];
    }

    true
}

// Use the DTM tables to find mate scores.
// Either DTZ or WDL must have been probed successfully earlier.
// A return value of 0 means that not all probes were successful.
fn root_probe_dtm(pos: &mut Position, root_moves: &mut RootMoves) -> bool {
    let mut success = 1;

    let mut tmp_score = Vec::new();

    // Probe each move
    for ref mut rm in root_moves.iter_mut() {
        // Use tb_score to find out if the position is won or lost
        let wdl = if rm.tb_score > PawnValueEg { 2 }
            else if rm.tb_score < -PawnValueEg { -2 }
            else { 0 };

        if wdl == 0 {
            tmp_score.push(Value::ZERO);
        } else {
            let gives_check = pos.gives_check(rm.pv[0]);
            pos.do_move(rm.pv[0], gives_check);
            let v = -probe_dtm(pos, -wdl, &mut success);
            pos.undo_move(rm.pv[0]);
            if success == 0 {
                return false;
            }
            tmp_score.push(if wdl > 0 { v - 1 } else { v + 1 });
        }
    }

    // All probes were successful. Now adjust TB scores and ranks.
    for (ref mut rm, &v) in root_moves.iter_mut().zip(tmp_score.iter()) {
        rm.tb_score = v;

        // Let rank correspond to mate score, except for critical moves
        // ranked 900, which we rank below all other mates for safety.
        // By ranking mates above 1000 or below -1000, we let the search
        // know it need not search those moves.
        rm.tb_rank = if rm.tb_rank == 900 { 1001 } else { v.0 };
    }

    true
}

pub fn expand_mate(pos: &mut Position, idx: usize) {
    let mut success = 1;
    let mut chk = 0;

    let mut v = pos.root_moves[idx].score;
    let mut wdl = if v > Value::ZERO { 2 } else { -2 };

    // First get to the end of the incomplete PV
    for i in 0..pos.root_moves[idx].pv.len() {
        let m = pos.root_moves[idx].pv[i];
        v = if v > Value::ZERO { -v - 1 } else { -v + 1 };
        wdl = -wdl;
        let gives_check = pos.gives_check(m);
        pos.do_move(m, gives_check);
    }

    // Now try to expand until the actual mate
    if popcount(pos.pieces()) <= cardinality_dtm() {
        while v != -Value::MATE {
            v = if v > Value::ZERO { -v - 1 } else { -v + 1 };
            wdl = -wdl;
            let mut best_move = Move::NONE;
            for m in MoveList::new(pos, GenType::Legal) {
                let gives_check = pos.gives_check(m);
                pos.do_move(m, gives_check);
                if wdl < 0 {
                    // We must check that the move is winning
                    chk = probe_wdl(pos, &mut success);
                }
                let w = if success != 0 && (wdl > 0 || chk < 0) {
                    probe_dtm(pos, wdl, &mut success)
                } else {
                    Value::ZERO
                };
                pos.undo_move(m);
                if success == 0 {
                    break;
                }
                if v == w {
                    best_move = m;
                    break;
                }
            }
            if success == 0 || best_move == Move::NONE {
                break;
            }
            pos.root_moves[idx].pv.push(best_move);
            let gives_check = pos.gives_check(best_move);
            pos.do_move(best_move, gives_check);
        }
    }

    // Move back to the root position
    for i in (0..pos.root_moves[idx].pv.len()).rev() {
        let m = pos.root_moves[idx].pv[i];
        pos.undo_move(m);
    }
}

pub fn rank_root_moves(pos: &mut Position, root_moves: &mut RootMoves) {
    let mut root_in_tb = false;
    let mut dtz_available = true;
    let mut dtm_available = false;

    if cardinality() >= popcount(pos.pieces())
        && !pos.has_castling_right(ANY_CASTLING)
    {
        // Try to rank moves using DTZ tables
        root_in_tb = root_probe_dtz(pos, root_moves);

        if !root_in_tb {
            // DTZ tables are missing
            dtz_available = false;

            // Try to rank moves using WDL tables as fallback
            root_in_tb = root_probe_wdl(pos, root_moves);
        }

        // If ranking was successful, try to obtain mate values from DTM tables
        if root_in_tb && cardinality_dtm() >= popcount(pos.pieces()) {
            dtm_available = root_probe_dtm(pos, root_moves);
        }
    }

    if root_in_tb { // Ranking was successful
        // Sort moves according to TB rank
        root_moves.sort();

        // Probe during search only if neither DTM nor DTZ is available
        // and we are winning.
        if dtm_available || dtz_available || root_moves[0].tb_rank <= 0 {
            unsafe {
                CARDINALITY = 0;
            }
        }
    } else {
        // Ranking was not successful, clean up
        for ref mut rm in root_moves.iter_mut() {
            rm.tb_rank = 0;
        }
    }

    unsafe {
        ROOT_IN_TB = root_in_tb;
    }
}

const OFF_DIAG: [i8; 64] = [
    0, -1, -1, -1, -1, -1, -1, -1,
    1,  0, -1, -1, -1, -1, -1, -1,
    1,  1,  0, -1, -1, -1, -1, -1,
    1,  1,  1,  0, -1, -1, -1, -1,
    1,  1,  1,  1,  0, -1, -1, -1,
    1,  1,  1,  1,  1,  0, -1, -1,
    1,  1,  1,  1,  1,  1,  0, -1,
    1,  1,  1,  1,  1,  1,  1,  0,
];

const TRIANGLE: [u8; 64] = [
    6, 0, 1, 2, 2, 1, 0, 6,
    0, 7, 3, 4, 4, 3, 7, 0,
    1, 3, 8, 5, 5, 8, 3, 1,
    2, 4, 5, 9, 9, 5, 4, 2,
    2, 4, 5, 9, 9, 5, 4, 2,
    1, 3, 8, 5, 5, 8, 3, 1,
    0, 7, 3, 4, 4, 3, 7, 0,
    6, 0, 1, 2, 2, 1, 0, 6,
];

const FLIP_DIAG: [u8; 64] = [
    0,  8, 16, 24, 32, 40, 48, 56,
    1,  9, 17, 25, 33, 41, 49, 57,
    2, 10, 18, 26, 34, 42, 50, 58,
    3, 11, 19, 27, 35, 43, 51, 59,
    4, 12, 20, 28, 36, 44, 52, 60,
    5, 13, 21, 29, 37, 45, 53, 61,
    6, 14, 22, 30, 38, 46, 54, 62,
    7, 15, 23, 31, 39, 47, 55, 63,
];

const LOWER: [u8; 64] = [
    28,  0,  1,  2,  3,  4,  5,  6,
     0, 29,  7,  8,  9, 10, 11, 12,
     1,  7, 30, 13, 14, 15, 16, 17,
     2,  8, 13, 31, 18, 19, 20, 21,
     3,  9, 14, 18, 32, 22, 23, 24,
     4, 10, 15, 19, 22, 33, 25, 26,
     5, 11, 16, 20, 23, 25, 34, 27,
     6, 12, 17, 21, 24, 26, 27, 35,
];

const DIAG: [u8; 64] = [
     0,  0,  0,  0,  0,  0,  0,  8,
     0,  1,  0,  0,  0,  0,  9,  0,
     0,  0,  2,  0,  0, 10,  0,  0,
     0,  0,  0,  3, 11,  0,  0,  0,
     0,  0,  0, 12,  4,  0,  0,  0,
     0,  0, 13,  0,  0,  5,  0,  0,
     0, 14,  0,  0,  0,  0,  6,  0,
    15,  0,  0,  0,  0,  0,  0,  7,
];

const FLAP: [u8; 64] = [
    0,  0,  0,  0,  0,  0,  0, 0,
    0,  6, 12, 18, 18, 12,  6, 0,
    1,  7, 13, 19, 19, 13,  7, 1,
    2,  8, 14, 20, 20, 14,  8, 2,
    3,  9, 15, 21, 21, 15,  9, 3,
    4, 10, 16, 22, 22, 16, 10, 4,
    5, 11, 17, 23, 23, 17, 11, 5,
    0,  0,  0,  0,  0,  0,  0, 0,
];

const PTWIST: [u8; 64] = [
     0,  0,  0,  0,  0,  0,  0,  0,
    47, 35, 23, 11, 10, 22, 34, 46,
    45, 33, 21,  9,  8, 20, 32, 44,
    43, 31, 19,  7,  6, 18, 30, 42,
    41, 29, 17,  5,  4, 16, 28, 40,
    39, 27, 15,  3,  2, 14, 26, 38,
    37, 25, 13,  1,  0, 12, 24, 36,
     0,  0,  0,  0,  0,  0,  0,  0
];

const FLAP2: [u8; 64] = [
     0,  0,  0,  0,  0,  0,  0,  0,
     0,  1,  2,  3,  3,  2,  1,  0,
     4,  5,  6,  7,  7,  6,  5,  4,
     8,  9, 10, 11, 11, 10,  9,  8,
    12, 13, 14, 15, 15, 14, 13, 12,
    16, 17, 18, 19, 19, 18, 17, 16,
    20, 21, 22, 23, 23, 22, 21, 20,
     0,  0,  0,  0,  0,  0,  0,  0,
];

const PTWIST2: [u8; 64] = [
     0,  0,  0,  0,  0,  0,  0,  0,
    47, 45, 43, 41, 40, 42, 44, 46,
    39, 37, 35, 33, 32, 34, 36, 38,
    31, 29, 27, 25, 24, 26, 28, 30,
    23, 21, 19, 17, 16, 18, 20, 22,
    15, 13, 11,  9,  8, 10, 12, 14,
     7,  5,  3,  1,  0,  2,  4,  6,
     0,  0,  0,  0,  0,  0,  0,  0,
];

const KK_IDX: [[u16; 64]; 10] = [
    [   0,   0,   0,   0,   1,   2,   3,   4,
        0,   0,   0,   5,   6,   7,   8,   9,
       10,  11,  12,  13,  14,  15,  16,  17,
       18,  19,  20,  21,  22,  23,  24,  25,
       26,  27,  28,  29,  30,  31,  32,  33,
       34,  35,  36,  37,  38,  39,  40,  41,
       42,  43,  44,  45,  46,  47,  48,  49,
       50,  51,  52,  53,  54,  55,  56,  57, ],
    [  58,   0,   0,   0,  59,  60,  61,  62,
       63,   0,   0,   0,  64,  65,  66,  67,
       68,  69,  70,  71,  72,  73,  74,  75,
       76,  77,  78,  79,  80,  81,  82,  83,
       84,  85,  86,  87,  88,  89,  90,  91,
       92,  93,  94,  95,  96,  97,  98,  99,
      100, 101, 102, 103, 104, 105, 106, 107,
      108, 109, 110, 111, 112, 113, 114, 115 ],
    [ 116, 117,   0,   0,   0, 118, 119, 120,
      121, 122,   0,   0,   0, 123, 124, 125,
      126, 127, 128, 129, 130, 131, 132, 133,
      134, 135, 136, 137, 138, 139, 140, 141,
      142, 143, 144, 145, 146, 147, 148, 149,
      150, 151, 152, 153, 154, 155, 156, 157,
      158, 159, 160, 161, 162, 163, 164, 165,
      166, 167, 168, 169, 170, 171, 172, 173 ],
    [ 174,   0,   0,   0, 175, 176, 177, 178,
      179,   0,   0,   0, 180, 181, 182, 183,
      184,   0,   0,   0, 185, 186, 187, 188,
      189, 190, 191, 192, 193, 194, 195, 196,
      197, 198, 199, 200, 201, 202, 203, 204,
      205, 206, 207, 208, 209, 210, 211, 212,
      213, 214, 215, 216, 217, 218, 219, 220,
      221, 222, 223, 224, 225, 226, 227, 228 ],
    [ 229, 230,   0,   0,   0, 231, 232, 233,
      234, 235,   0,   0,   0, 236, 237, 238,
      239, 240,   0,   0,   0, 241, 242, 243,
      244, 245, 246, 247, 248, 249, 250, 251,
      252, 253, 254, 255, 256, 257, 258, 259,
      260, 261, 262, 263, 264, 265, 266, 267,
      268, 269, 270, 271, 272, 273, 274, 275,
      276, 277, 278, 279, 280, 281, 282, 283 ],
    [ 284, 285, 286, 287, 288, 289, 290, 291,
      292, 293,   0,   0,   0, 294, 295, 296,
      297, 298,   0,   0,   0, 299, 300, 301,
      302, 303,   0,   0,   0, 304, 305, 306,
      307, 308, 309, 310, 311, 312, 313, 314,
      315, 316, 317, 318, 319, 320, 321, 322,
      323, 324, 325, 326, 327, 328, 329, 330,
      331, 332, 333, 334, 335, 336, 337, 338 ],
    [   0,   0, 339, 340, 341, 342, 343, 344,
        0,   0, 345, 346, 347, 348, 349, 350,
        0,   0, 441, 351, 352, 353, 354, 355,
        0,   0,   0, 442, 356, 357, 358, 359,
        0,   0,   0,   0, 443, 360, 361, 362,
        0,   0,   0,   0,   0, 444, 363, 364,
        0,   0,   0,   0,   0,   0, 445, 365,
        0,   0,   0,   0,   0,   0,   0, 446 ],
    [   0,   0,   0, 366, 367, 368, 369, 370,
        0,   0,   0, 371, 372, 373, 374, 375,
        0,   0,   0, 376, 377, 378, 379, 380,
        0,   0,   0, 447, 381, 382, 383, 384,
        0,   0,   0,   0, 448, 385, 386, 387,
        0,   0,   0,   0,   0, 449, 388, 389,
        0,   0,   0,   0,   0,   0, 450, 390,
        0,   0,   0,   0,   0,   0,   0, 451 ],
    [ 452, 391, 392, 393, 394, 395, 396, 397,
        0,   0,   0,   0, 398, 399, 400, 401,
        0,   0,   0,   0, 402, 403, 404, 405,
        0,   0,   0,   0, 406, 407, 408, 409,
        0,   0,   0,   0, 453, 410, 411, 412,
        0,   0,   0,   0,   0, 454, 413, 414,
        0,   0,   0,   0,   0,   0, 455, 415,
        0,   0,   0,   0,   0,   0,   0, 456 ],
    [ 457, 416, 417, 418, 419, 420, 421, 422,
        0, 458, 423, 424, 425, 426, 427, 428,
        0,   0,   0,   0,   0, 429, 430, 431,
        0,   0,   0,   0,   0, 432, 433, 434,
        0,   0,   0,   0,   0, 435, 436, 437,
        0,   0,   0,   0,   0, 459, 438, 439,
        0,   0,   0,   0,   0,   0, 460, 440,
        0,   0,   0,   0,   0,   0,   0, 461 ],
];

static mut BINOMIAL: [[u32; 64]; 6] = [[0; 64]; 6];
static mut PAWN_IDX: [[u32; 24]; 5] = [[0; 24]; 5];
static mut PFACTOR: [[u32; 4]; 5] = [[0; 4]; 5];
static mut PAWN_IDX2: [[u32; 24]; 5] = [[0; 24]; 5];
static mut PFACTOR2: [[u32; 6]; 5] = [[0; 6]; 5];

fn off_diag(s: Square) -> i8 {
    OFF_DIAG[s.0 as usize]
}

fn is_off_diag(s: Square) -> bool {
    off_diag(s) != 0
}

fn triangle(s: Square) -> usize {
    TRIANGLE[s.0 as usize] as usize
}

fn flip_diag(s: Square) -> Square {
    Square(FLIP_DIAG[s.0 as usize] as u32)
}

fn lower(s: Square) -> usize {
    LOWER[s.0 as usize] as usize
}

fn diag(s: Square) -> usize {
    DIAG[s.0 as usize] as usize
}

fn skip(s1: Square, s2: Square) -> usize {
    (s1.0 > s2.0) as usize
}

fn flap(s: Square) -> usize {
    FLAP[s.0 as usize] as usize
}

fn ptwist(s: Square) -> usize {
    PTWIST[s.0 as usize] as usize
}

fn flap2(s: Square) -> usize {
    FLAP2[s.0 as usize] as usize
}

fn ptwist2(s: Square) -> usize {
    PTWIST2[s.0 as usize] as usize
}

fn kk_idx(s1: usize, s2: Square) -> usize {
    KK_IDX[s1][s2.0 as usize] as usize
}

fn binomial(n: usize, k: usize) -> usize {
    unsafe { BINOMIAL[k as usize][n] as usize }
}

fn pawn_idx(num: usize, s: usize) -> usize {
    unsafe { PAWN_IDX[num][s] as usize }
}

fn pfactor(num: usize, s: usize) -> usize {
    unsafe { PFACTOR[num][s] as usize }
}

fn pawn_idx2(num: usize, s: usize) -> usize {
    unsafe { PAWN_IDX2[num][s] as usize }
}

fn pfactor2(num: usize, s: usize) -> usize {
    unsafe { PFACTOR2[num][s] as usize }
}

fn init_indices() {
    for i in 0..6 {
        for j in 0..64 {
            let mut f = 1i32;
            let mut l = 1i32;
            for k in 0..i {
                f *= (j as i32) - (k as i32);
                l *= (k as i32) + 1;
            }
            unsafe { BINOMIAL[i][j] = (f / l) as u32; }
        }
    }

    for i in 0..5 {
        let mut s = 0;
        for j in 0..24 {
            unsafe { PAWN_IDX[i][j] = s as u32; }
            let k = (1 + (j % 6)) * 8 + (j / 6);
            s += binomial(ptwist(Square(k as u32)), i);
            if (j + 1) % 6 == 0 {
                unsafe { PFACTOR[i][j / 6] = s as u32; }
                s = 0;
            }
        }
    }

    for i in 0..5 {
        let mut s = 0;
        for j in 0..24 {
            unsafe { PAWN_IDX2[i][j] = s as u32; }
            let k = (1 + (j / 4)) * 8 + (j % 4);
            s += binomial(ptwist2(Square(k as u32)), i);
            if (j + 1) % 4 == 0 {
                unsafe { PFACTOR2[i][j / 4] = s as u32; }
                s = 0;
            }
        }
    }
}

fn encode_piece(p: &mut [Square; 6], ei: &EncInfo, entry: &PieceEntry) -> usize {
    let n = entry.num as usize;

    // normalize
    if p[0].0 & 4 != 0 {
        for i in 0..n {
            p[i] = Square(p[i].0 ^ 0x07);
        }
    }
    if p[0].0 & 0x20 != 0 {
        for i in 0..n {
            p[i] = Square(p[i].0 ^ 0x38);
        }
    }

    for i in 0..n {
        if is_off_diag(p[i]) {
            if off_diag(p[i]) > 0
                && i < (if entry.kk_enc { 2 } else { 3 })
            {
                for j in i..n {
                    p[j] = flip_diag(p[j]);
                }
            }
            break;
        }
    }

    let mut i;
    let mut idx = if entry.kk_enc {
        i = 2;
        kk_idx(triangle(p[0]), p[1])
    } else {
        i = 3;
        let s1 = skip(p[1], p[0]);
        let s2 = skip(p[2], p[0]) + skip(p[2], p[1]);
        if is_off_diag(p[0]) {
            triangle(p[0]) * 63*62 + (p[1].0 as usize - s1) * 62
            + (p[2].0 as usize - s2)
        } else if is_off_diag(p[1]) {
            6*63*62 + diag(p[0]) * 28*62 + lower(p[1]) * 62
            + p[2].0 as usize - s2
        } else if is_off_diag(p[2]) {
            6*63*62 + 4*28*62 + diag(p[0]) * 7*28
            + (diag(p[1]) - s1) * 28 + lower(p[2])
        } else {
            6*63*62 + 4*28*62 + 4*7*28 + diag(p[0]) * 7*6
            + (diag(p[1]) - s1) * 6 + (diag(p[2]) - s2)
        }
    };
    idx *= ei.factor[0] as usize;

    while i < n {
        let t = ei.norm[i] as usize;
        for j in i..i+t {
            for k in j+1..i+t {
                if p[j] > p[k] {
                    p.swap(j, k);
                }
            }
        }
        let mut s = 0;
        for m in i..i+t {
            let sq = p[m];
            let mut skips = 0;
            for l in 0..i {
                skips += skip(sq, p[l]);
            }
            s += binomial(sq.0 as usize - skips, m - i + 1);
        }
        idx += s * ei.factor[i] as usize;
        i += t;
    }

    idx
}

fn leading_pawn_file(pawns: Bitboard) -> File {
    if pawns & (FILEA_BB | FILEB_BB | FILEG_BB | FILEH_BB) != 0 {
        if pawns & (FILEA_BB | FILEH_BB) != 0 { FILE_A } else { FILE_B }
    } else {
        if pawns & (FILEC_BB | FILEF_BB) != 0 { FILE_C } else { FILE_D }
    }
}

fn encode_pawn(p: &mut [Square; 6], ei: &EncInfo, entry: &PawnEntry) -> usize {
    let n = entry.num as usize;

    // normalize
    if p[0].0 & 4 != 0 {
        for i in 0..n {
            p[i] = Square(p[i].0 ^ 0x07);
        }
    }
    for i in 0..entry.pawns[0] {
        for j in i+1..entry.pawns[0] {
            if ptwist(p[i as usize]) < ptwist(p[j as usize]) {
                p.swap(i as usize, j as usize);
            }
        }
    }

    let t = entry.pawns[0] as usize;
    let mut idx = pawn_idx(t - 1, flap(p[0])) as usize;
    for i in 1..t {
        idx += binomial(ptwist(p[i]), t - i);
    }
    idx *= ei.factor[0] as usize;

    // remaining pawns
    let mut i = entry.pawns[0] as usize;
    let t = i + entry.pawns[1] as usize;
    if t > i {
        for j in i..t {
            for k in j+1..t {
                if p[j].0 > p[k].0 {
                    p.swap(j, k);
                }
            }
        }
        let mut s = 0;
        for m in i..t {
            let sq = p[m];
            let mut skips = 0;
            for k in 0..i {
                skips += skip(sq, p[k]);
            }
            s += binomial(sq.0 as usize - skips - 8, m - i + 1);
        }
        idx += s * ei.factor[i] as usize;
        i = t;
    }

    while i < n {
        let t = ei.norm[i] as usize;
        for j in i..i+t {
            for k in j+1..i+t {
                if p[j] > p[k] {
                    p.swap(j, k);
                }
            }
        }
        let mut s = 0;
        for m in i..i+t {
            let sq = p[m];
            let mut skips = 0;
            for k in 0..i {
                skips += skip(sq, p[k]);
            }
            s += binomial(sq.0 as usize - skips, m - i + 1);
        }
        idx += s * ei.factor[i] as usize;
        i += t;
    }

    idx
}

fn leading_pawn_rank(pawns: Bitboard, flip: bool) -> Rank {
    let b = if flip { Bitboard(pawns.0.swap_bytes()) } else { pawns };
    lsb(b).rank() - 1
}

fn encode_pawn2(p: &mut [Square; 6], ei: &EncInfo, entry: &PawnEntry) -> usize {
    let n = entry.num as usize;

    // normalize
    if p[0].0 & 4 != 0 {
        for i in 0..n {
            p[i] = Square(p[i].0 ^ 0x07);
        }
    }
    for i in 0..entry.pawns[0] {
        for j in i+1..entry.pawns[0] {
            if ptwist2(p[i as usize]) < ptwist2(p[j as usize]) {
                p.swap(i as usize, j as usize);
            }
        }
    }

    let t = entry.pawns[0] as usize;
    let mut idx = pawn_idx2(t - 1, flap2(p[0])) as usize;
    for i in 1..t {
        idx += binomial(ptwist2(p[i]), t - i);
    }
    idx *= ei.factor[0] as usize;

    // remaining pawns
    let mut i = entry.pawns[0] as usize;
    let t = i + entry.pawns[1] as usize;
    if t > i {
        for j in i..t {
            for k in j+1..t {
                if p[j].0 > p[k].0 {
                    p.swap(j, k);
                }
            }
        }
        let mut s = 0;
        for m in i..t {
            let sq = p[m];
            let mut skips = 0;
            for k in 0..i {
                skips += skip(sq, p[k]);
            }
            s += binomial(sq.0 as usize - skips - 8, m - i + 1);
        }
        idx += s * ei.factor[i] as usize;
        i = t;
    }

    while i < n {
        let t = ei.norm[i] as usize;
        for j in i..i+t {
            for k in j+1..i+t {
                if p[j] > p[k] {
                    p.swap(j, k);
                }
            }
        }
        let mut s = 0;
        for m in i..i+t {
            let sq = p[m];
            let mut skips = 0;
            for k in 0..i {
                skips += skip(sq, p[k]);
            }
            s += binomial(sq.0 as usize - skips, m - i + 1);
        }
        idx += s * ei.factor[i] as usize;
        i += t;
    }

    idx
}

fn decompress_pairs(d: &PairsData, idx: usize) -> u32 {
    if d.idx_bits == 0 {
        return d.const_val as u32;
    }

    let main_idx = (idx >> d.idx_bits) as isize;
    let mut lit_idx  =
        (idx as isize & ((1isize << d.idx_bits) - 1))
        - (1isize << (d.idx_bits - 1));
    let mut block = unsafe {
        u32::from_le((*d.index_table.offset(main_idx)).block) as isize
    };
    let idx_offset = unsafe {
        u16::from_le((*d.index_table.offset(main_idx)).offset)
    };
    lit_idx += idx_offset as isize;

    while lit_idx < 0 {
        block -= 1;
        lit_idx += unsafe { *d.size_table.offset(block) as isize } + 1;
    }
    while lit_idx > unsafe { *d.size_table.offset(block) as isize } {
        lit_idx -= unsafe { *d.size_table.offset(block) as isize } + 1;
        block += 1;
    }

    let mut ptr = unsafe { d.data.offset(block << d.block_size) } as *const u32;

    let mut code = unsafe { u64::from_be(*(ptr as *const u64)) };
    ptr = unsafe { ptr.offset(2) };
    let mut bit_cnt = 0;
    let mut sym;
    loop {
        let mut l = 0;
        while code < d.base[l] {
            l += 1;
        }
        l += d.min_len as usize;
        sym = unsafe { u16::from_le(*d.offset.offset(l as isize)) as isize };
        sym += ((code - d.base[l - d.min_len as usize]) >> (64 - l)) as isize;
        if lit_idx < d.sym_len[sym as usize] as isize + 1 {
            break;
        }
        lit_idx -= d.sym_len[sym as usize] as isize + 1;
        code <<= l;
        bit_cnt += l;
        if bit_cnt >= 32 {
            bit_cnt -= 32;
            code |= (unsafe { u32::from_be(*ptr) } as u64) << bit_cnt;
            ptr = unsafe { ptr.offset(1) };
        }
    }

    while d.sym_len[sym as usize] != 0 {
        let w = unsafe { d.sym_pat.offset(3 * sym) };
        let s1 = s1(w);
        if lit_idx < d.sym_len[s1] as isize + 1 {
            sym = s1 as isize;
        } else {
            lit_idx -= d.sym_len[s1] as isize + 1;
            sym = s2(w) as isize;
        }
    }

    unsafe { s1(d.sym_pat.offset(3 * sym)) as u32 }
}