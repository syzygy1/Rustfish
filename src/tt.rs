// SPDX-License-Identifier: GPL-3.0-or-later

use types::*;

use std;

// TTEntry struct is the 10 bytes transposition-table entry, defined as below:
//
// key        16 bit
// move       16 bit
// value      16 bit
// eval value 16 bit
// generation  6 bit
// bound type  2 bit
// depth       8 bit

pub struct TTEntry {
    key16: u16,
    move16: u16,
    value16: i16,
    eval16: i16,
    gen_bound8: u8,
    depth8: i8,
}

impl TTEntry {
    pub fn mov(&self) -> Move {
        Move(self.move16 as u32)
    }

    pub fn value(&self) -> Value {
        Value(self.value16 as i32)
    }

    pub fn eval(&self) -> Value {
        Value(self.eval16 as i32)
    }

    pub fn depth(&self) -> Depth {
        Depth(self.depth8 as i32)
    }

    pub fn bound(&self) -> Bound {
        Bound((self.gen_bound8 & 3) as u32)
    }

    pub fn save(
        &mut self, k: Key, v: Value, b: Bound, d: Depth, m: Move, ev: Value,
        g: u8
    ) {
        debug_assert!(d / ONE_PLY * ONE_PLY == d);

        let k16 = (k.0 >> 48) as u16;

        // Preserve any existing move for the same position
        if m != Move::NONE || k16 != self.key16 {
            self.move16 = m.0 as u16;
        }

        // Don't overwrite more valuable entries
        if k16 != self.key16
            || (d / ONE_PLY) as i8 > self.depth8 - 4
            || b == Bound::EXACT
        {
            self.key16 = k16;
            self.value16 = v.0 as i16;
            self.eval16 = ev.0 as i16;
            self.gen_bound8 = g | (b.0 as u8);
            self.depth8 = (d / ONE_PLY) as i8;
        }
    }
}

// The transposition table consists of a power of 2 number of clusters.
// Each cluster consists of ClusterSize number of TTEntry. Each non-empty
// entry contains information about exactly one position. The size of a
// cluster should divide the size of a cache line size, to ensure that
// clusters never cross cache lines. This ensures best cache performance,
// as the cacheline is prefetched, as soon as possible.

const CLUSTER_SIZE: usize = 3;

struct Cluster {
    entry: [TTEntry; CLUSTER_SIZE],
    _padding: [u8; 2], // Align to a divisor of the cache line size
}

static mut CLUSTER_COUNT: usize = 0;
static mut TABLE: *mut Cluster = 0 as *mut Cluster;
static mut TABLE_CAP: usize = 0;
static mut GENERATION8: u8 = 0;

pub fn new_search() {
    unsafe {
        GENERATION8 += 4; // Lower two bits are used by bound
    }
}

pub fn generation() -> u8 {
    unsafe { GENERATION8 }
}

// The lowest order bits of the key are used to get the index of the cluster
fn cluster(key: Key) -> &'static mut Cluster {
    unsafe {
        let p: *mut Cluster =
            TABLE.offset((((key.0 as u32 as u64) *
                (CLUSTER_COUNT as u64)) >> 32) as isize);
        let c: &'static mut Cluster = &mut *p;
        c
    }
}

// tt::resize() sets the size of the transposition table, measured in
// megabytes. The transposition table consists of a power of 2 number of
// clusters and each cluster consists of CLUSTER_SIZE number of TTEntry.

pub fn resize(mb_size: usize) {
    let new_cluster_count =
        mb_size * 1024 * 1024 / std::mem::size_of::<Cluster>();

    unsafe {
        if new_cluster_count == CLUSTER_COUNT {
            return;
        }

        free();

        CLUSTER_COUNT = new_cluster_count;

        let mut v: Vec<Cluster> = Vec::with_capacity(new_cluster_count);
        TABLE = v.as_mut_ptr();
        TABLE_CAP = v.capacity();
        // forget in order to prevent deallocation by dropping
        std::mem::forget(v);
    }
}

// tt::free() deallocates the transposition table.

pub fn free() {
    unsafe {
        if !TABLE.is_null() {
            let _ = Vec::from_raw_parts(TABLE, 0, TABLE_CAP);
            // deallocate by dropping
        }
    }
}

// tt::clear() clears the entire transposition table. It is called whenever
// the table is resized or when the user asks the program to clear the table
// (via the UCI interface).

pub fn clear() {
    let tt_slice = unsafe {
        std::slice::from_raw_parts_mut(TABLE, CLUSTER_COUNT)
    };

    for cluster in tt_slice.iter_mut() {
        for tte in cluster.entry.iter_mut() {
            tte.key16 = 0;
            tte.move16 = 0;
            tte.value16 = 0;
            tte.eval16 = 0;
            tte.gen_bound8 = 0;
            tte.depth8 = 0;
            tte.key16 = 0;
        }
    }
}

// tt::probe() looks up the current position in the transposition table. It
// returns true and a pointer to the TTentry if the position is found.
// Otherwise, it returns false and a pointer to an empty or least valuable
// TTEntry to be replaced later. The replace value of an entry is calculated
// as its depth minus 8 times its relative age. TTEntry t1 is considered more
// valuable than TTEntry t2 if its replace value is greater than that of t2.

pub fn probe(key: Key) -> (&'static mut TTEntry, bool) {
    let cl = cluster(key);
    // Use the high 16 bits of the hash key as key inside the cluster
    let key16 = (key.0 >> 48) as u16;

    for i in 0..CLUSTER_SIZE {
        if cl.entry[i].key16 == 0 || cl.entry[i].key16 == key16 {
            if cl.entry[i].gen_bound8 & 0xfc != generation()
                && cl.entry[i].key16 != 0
            {
                cl.entry[i].gen_bound8 =
                    generation() | (cl.entry[i].bound().0 as u8);
            }
            let found = cl.entry[i].key16 != 0;
            return (&mut (cl.entry[i]), found);
        }
    }

    // Find an entry to be replaced according to the replacement strategy
    let mut r = 0;
    for i in 1..CLUSTER_SIZE {
        // Due to our packed storage format for generation and its cyclic
        // nature we add 259 (256 is the modulus plus 3 to keep the lowest
        // two bound bits from affecting the result) to calculate the entry
        // age correctly even after generation8 overflows into the next cycle.
        if (cl.entry[r].depth8 as i32) -
                ((259 + (generation() as i32) -
                        (cl.entry[r].gen_bound8 as i32)) & 0xfc) * 2
            > (cl.entry[i].depth8 as i32) -
                ((259 + (generation() as i32) -
                        (cl.entry[i].gen_bound8 as i32)) & 0xfc) * 2
        {
            r = i;
        }
    }

    (&mut (cl.entry[r]), false)
}

// tt::hashfull() returns an approximation of the hashtable occupation during
// a search. The hash is x permill full, as per UCI protocol.

pub fn hashfull() -> i32 {
    let tt_slice = unsafe {
        std::slice::from_raw_parts(TABLE, 1000 / CLUSTER_SIZE)
    };

    let mut cnt = 0;

    for cluster in tt_slice.iter() {
        for tte in cluster.entry.iter() {
            if tte.gen_bound8 & 0xfc == generation() {
                cnt += 1;
            }
        }
    }

    cnt
}
