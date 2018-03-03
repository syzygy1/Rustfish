// SPDX-License-Identifier: GPL-3.0-or-later

use search;
use types::*;
use ucioption;

use std;

static mut START_TIME: Option<std::time::Instant> = None;
static mut OPTIMUM_TIME: i64 = 0;
static mut MAXIMUM_TIME: i64 = 0;

pub fn optimum() -> i64 {
    unsafe { OPTIMUM_TIME }
}

pub fn maximum() -> i64 {
    unsafe { MAXIMUM_TIME }
}

pub fn elapsed() -> i64 {
    let duration = unsafe { START_TIME.unwrap().elapsed() };
    (duration.as_secs() * 1000 + (duration.subsec_nanos() / 1000000) as u64)
        as i64
}

#[derive(PartialEq, Eq)]
enum TimeType { OptimumTime, MaxTime }
use self::TimeType::*;

// Plan time management at most this many moves ahread
const MOVE_HORIZON: i32 = 50;
// When in trouble, we can step over reserved time with this ratio
const MAX_RATIO: f64 = 7.3;
// But we must not steal time from remaining moves over this ratio
const STEAL_RATIO: f64 = 0.34;

// importance() is a skew-logistic function based on naive statistical
// analysis of "how many games are still undecided after n half moves".
// The game is considered "undecided" as long as neither side has >275cp
// advantage. Data was extracted from the CCRL game database with some
// simply filtering criteria.

fn importance(ply: i32) -> f64 {
    const XSCALE: f64 = 6.85;
    const XSHIFT: f64 = 64.5;
    const SKEW:   f64 = 0.171;

    (1. + ((ply as f64 - XSHIFT) / XSCALE).exp()).powf(-SKEW)
    + std::f64::MIN_POSITIVE
}

fn remaining(
    my_time: i64, movestogo: i32, ply: i32, slow_mover: i64,
    time_type: TimeType
) -> i64 {
    let max_ratio = if time_type == OptimumTime { 1. } else { MAX_RATIO };
    let steal_ratio = if time_type == OptimumTime { 0. } else { STEAL_RATIO };

    let move_importance = (importance(ply) * slow_mover as f64) / 100.;
    let mut other_moves_importance = 0.;

    for i in 1..movestogo {
        other_moves_importance += importance(ply + 2 * i);
    }

    let ratio1 = (max_ratio * move_importance) /
        (max_ratio * move_importance + other_moves_importance);
    let ratio2 = (move_importance + steal_ratio * other_moves_importance) /
        (move_importance + other_moves_importance);

    (my_time as f64 * ratio1.min(ratio2)) as i64
}

// init() is called at the beginning of the search and calculates the allowed
// thinking time out of the time control and current game ply. We support
// four different kinds of time controls, passed in 'limits':
//
//  inc == 0 && movestogo == 0 means: x basetime  [sudden death!]
//  inc == 0 && movestogo != 0 means: x moves in y minutes
//  inc >  0 && movestogo == 0 means: x basetime + z increment
//  inc >  0 && movestogo != 0 means: x moves in y minutes + z increment

pub fn init(limits: &mut search::LimitsType, us: Color, ply: i32)
{
    let min_think_time = ucioption::get_i32("Minimum Thinking Time") as i64;
    let move_overhead  = ucioption::get_i32("Move Overhead") as i64;
    let slow_mover     = ucioption::get_i32("Slow Mover") as i64;

    unsafe {
        START_TIME = limits.start_time;
        let time = std::cmp::max(limits.time[us.0 as usize], min_think_time);
        OPTIMUM_TIME = time;
        MAXIMUM_TIME = time;
    }

    let max_mtg = if limits.movestogo != 0
        { std::cmp::min(limits.movestogo, MOVE_HORIZON) }
    else
        { MOVE_HORIZON };

    // We calculate optimum time usage for different hypothetical "moves to go"
    // values and choose the minimum of calculated search time values. Usually
    // the greates hyp_mtg givse the minimum values.
    for hyp_mtg in 1..(max_mtg + 1) {
        // Calculate thinking time for hypothetical "moves to go" value
        let mut hyp_my_time = limits.time[us.0 as usize]
            + limits.inc[us.0 as usize] * (hyp_mtg - 1) as i64
            - move_overhead * (2 + std::cmp::min(hyp_mtg, 40) as i64);

        hyp_my_time = std::cmp::max(hyp_my_time, 0);

        let t1 = min_think_time
            + remaining(hyp_my_time, hyp_mtg, ply, slow_mover, OptimumTime);
        let t2 = min_think_time
            + remaining(hyp_my_time, hyp_mtg, ply, slow_mover, MaxTime);

        unsafe {
            OPTIMUM_TIME = std::cmp::min(t1, OPTIMUM_TIME);
            MAXIMUM_TIME = std::cmp::min(t2, MAXIMUM_TIME);
        }
    }

    if ucioption::get_bool("Ponder") {
        unsafe {
            OPTIMUM_TIME += OPTIMUM_TIME / 4;
        }
    }
}
