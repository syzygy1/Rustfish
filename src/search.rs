// SPDX-License-Identifier: GPL-3.0-or-later

use bitboard::*;
use evaluate;
use evaluate::evaluate;
use movegen::*;
use movepick::*;
use position::*;
use tb;
use threads;
use timeman;
use tt;
use types::*;
use uci;
use ucioption;

use std;
use std::io::stdout;
use std::io::Write;
use std::time::Instant;

pub const CM_THRESHOLD: i32 = 0;

pub struct Stack {
    pv: Vec<Move>,
    pub cont_history: &'static PieceToHistory,
    ply: i32,
    pub current_move: Move,
    excluded_move: Move,
    pub killers: [Move; 2],
    static_eval: Value,
    stat_score: i32,
    move_count: i32,
}

#[derive(Clone, Eq)]
pub struct RootMove {
    pub score: Value,
    pub previous_score: Value,
    pub tb_score: Value,
    pub tb_rank: i32,
    pub sel_depth: i32,
    pub pv: Vec<Move>,
}

impl RootMove {
    pub fn new(m: Move) -> RootMove {
        RootMove {
            score: -Value::INFINITE,
            previous_score: -Value::INFINITE,
            tb_score: Value::ZERO,
            tb_rank: 0,
            sel_depth: 0,
            pv: vec![m],
        }
    }
}

impl Ord for RootMove {
    fn cmp(&self, other: &RootMove) -> std::cmp::Ordering {
        match self.tb_rank.cmp(&other.tb_rank) {
            std::cmp::Ordering::Equal => {
                match self.score.cmp(&other.score) {
                    std::cmp::Ordering::Equal => {
                        self.previous_score.cmp(&other.previous_score)
                    }
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

impl PartialOrd for RootMove {
    fn partial_cmp(&self, other: &RootMove) -> Option<std::cmp::Ordering> {
        Some(other.cmp(self))
    }
}

impl PartialEq for RootMove {
    fn eq(&self, other: &RootMove) -> bool {
        self.score == other.score && self.previous_score == other.previous_score
    }
}

pub type RootMoves = Vec<RootMove>;

#[derive(Clone)]
pub struct LimitsType {
    pub time: [i64; 2],
    pub inc: [i64; 2],
    pub movestogo: i32,
    pub depth: u32,
    pub movetime: i64,
    pub mate: u32,
    pub perft: u32,
    pub infinite: bool,
    pub nodes: u64,
    pub start_time: Option<Instant>,
}

impl LimitsType {
    pub fn new() -> LimitsType {
        LimitsType {
            time: [0; 2],
            inc: [0; 2],
            movestogo: 0,
            depth: 0,
            movetime: 0,
            mate: 0,
            perft: 0,
            infinite: false,
            nodes: 0,
            start_time: Some(Instant::now()),
        }
    }

    pub fn use_time_management(&self) -> bool {
        self.mate == 0 && self.movetime == 0 && self.depth == 0
        && self.nodes == 0 && self.perft == 0 && !self.infinite
    }
}

pub static mut LIMITS: LimitsType = LimitsType {
    time: [0; 2],
    inc: [0; 2],
    movestogo: 0,
    depth: 0,
    movetime: 0,
    mate: 0,
    perft: 0,
    infinite: false,
    nodes: 0,
    start_time: None,
};

pub fn limits() -> &'static mut LimitsType {
    unsafe {
        &mut LIMITS
    }
}

// Different node types
#[derive(Clone, Copy, PartialEq, Eq)]
struct NonPv;
struct Pv;

const NON_PV: usize = 0;
const PV: usize = 1;

trait NodeType {
    fn node_type() -> usize;
}

impl NodeType for NonPv {
    fn node_type() -> usize { NON_PV }
}

impl NodeType for Pv {
    fn node_type() -> usize { PV }
}

// Sizes and phases of the skip blocks, used for distributing search depths
// across the threads
const SKIP_SIZE: [i32; 20] =
    [ 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4 ];
const SKIP_PHASE: [i32; 20] =
    [ 0, 1, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7 ];

fn futility_margin(d: Depth) -> Value {
    Value(150 * d / ONE_PLY)
}

fn razor_margin() -> Value {
    Value(600)
}

// Futility and reductions lookup tables, initialized at startup
static mut FUTILITY_MOVE_COUNTS: [[i32; 16]; 2] = [[0; 16]; 2];
static mut REDUCTIONS: [[[[i32; 64]; 64]; 2]; 2] = [[[[0; 64]; 64]; 2]; 2];

fn reduction<PvNode: NodeType>(i: bool, d: Depth, mn: i32) -> Depth {
    unsafe {
        REDUCTIONS[PvNode::node_type()][i as usize]
            [std::cmp::min(d / ONE_PLY, 63) as usize]
            [std::cmp::min(mn, 63) as usize] * ONE_PLY
    }
}

fn futility_move_counts(i: bool, d: Depth) -> i32 {
    unsafe { FUTILITY_MOVE_COUNTS[i as usize][(d / ONE_PLY) as usize] }
}

// History and stats update bonus, based on depth
fn stat_bonus(depth: Depth) -> i32 {
    let d = depth / ONE_PLY;
    if d > 17 { 0 } else { d * d + 2 * d - 2 }
}

// perft() is our utility to verify move generation. All the leaf nodes up
// to the given depth are generated and counted, and the sum is returned.
fn perft<Root: Bool>(pos: &mut Position, depth: Depth) -> u64 {
    let mut nodes = 0u64;
    let leaf = depth == 2 * ONE_PLY;

    for m in MoveList::new::<Legal>(pos) {
        let cnt;
        if Root::bool() && depth <= ONE_PLY {
            cnt = 1;
            nodes += 1;
        } else {
            let checks = pos.gives_check(m);
            pos.do_move(m, checks);
            cnt = if leaf { MoveList::new::<Legal>(pos).size() as u64 }
                else { perft::<False>(pos, depth - ONE_PLY) };
            nodes += cnt;
            pos.undo_move(m);
        }
        if Root::bool() {
            println!("{}: {}", uci::move_str(m, pos.is_chess960()), cnt);
            stdout().flush().unwrap();
        }
    }
    nodes
}

// search::init() is called during startup to initialize various lookup tables

pub fn init() {
    unsafe {
        for imp in 0..2 {
            for d in 1..64 {
                for mc in 1..64 {
                    let r = (d as f64).ln() * (mc as f64).ln() / 1.95;

                    REDUCTIONS[NON_PV][imp][d][mc] = r.round() as i32;
                    REDUCTIONS[PV][imp][d][mc] = std::cmp::max(
                        REDUCTIONS[NON_PV][imp][d][mc] - 1, 0);

                    if imp == 0
                        && REDUCTIONS[NON_PV][imp][d][mc] >= 2
                    {
                        REDUCTIONS[NON_PV][imp][d][mc] += 1;
                    }
                }
            }
        }

        for d in 0..16 {
            FUTILITY_MOVE_COUNTS[0][d] =
                (2.4 + 0.74 * (d as f64).powf(1.78)) as i32;
            FUTILITY_MOVE_COUNTS[1][d] =
                (5.0 + 1.00 * (d as f64).powf(2.00)) as i32;
        }
    }
}

// search::clear() resets search state to its initial value

pub fn clear() {
    threads::wait_for_all();
    tt::clear();
    threads::clear_search();
    threads::wait_for_all();
}

// mainthread_search() is called by the main thread when the program
// received the UCI 'go' command. It searches from the root position and
// outputs the "bestmove".

pub fn mainthread_search(pos: &mut Position, th: &threads::ThreadCtrl) {
    if limits().perft != 0 {
        let nodes = perft::<True>(pos, (limits().perft as i32) * ONE_PLY);
        println!("\nNodes searched: {}", nodes);
        return;
    }

    let us = pos.side_to_move();
    timeman::init(limits(), us, pos.game_ply());
    tt::new_search();

    let analyzing = limits().infinite || ucioption::get_bool("UCI_AnalyseMode");

    // When analyzing, use contempt only if the user has said so
    let contempt =
        if !analyzing || ucioption::get_bool("Analysis Contempt") {
            ucioption::get_i32("Contempt") * PawnValueEg / 100
        } else {
            Value::ZERO
        };

    let contempt = Score::make(contempt.0, contempt.0 / 2);

    unsafe {
        evaluate::CONTEMPT = if analyzing || us == WHITE { contempt }
            else { -contempt }
    }

    if pos.root_moves.is_empty() {
        pos.root_moves.push(RootMove::new(Move::NONE));
        println!("info depth 0 score {}", uci::value(
            if pos.checkers() != 0 { -Value::MATE } else { Value::DRAW }));
        stdout().flush().unwrap();
    } else {
        threads::wake_up_slaves();

        thread_search(pos, th); // Let's start searching!
    }

    // When we reach the maximum depth, we can arrive here without
    // threads::stop() having been raised. However, if we are pondering or
    // if we are in an infinite search, the UCI protocol states that we
    // shouldn't print the best move before the GUI sends a "stop" or
    // "ponderhit" command. We therefore simply wait here until the GUI sends
    // one of those commands (which also raised threads::stop()).
    threads::set_stop_on_ponderhit(true);

    while !threads::stop() && (threads::ponder() || limits().infinite) {
    } // Busy wait for a stop or a ponder reset

    // Stop the threads if not already stopped (also raise the stop if
    // "ponderhit" has just reset threads::ponder()).
    threads::set_stop(true);

    // Wait until all threads have finished
    threads::wait_for_slaves();

    // Check if there are threads with a better score than main thread
    if ucioption::get_i32("MultiPV") == 1
        && limits().depth == 0
        && pos.root_moves[0].pv[0] != Move::NONE
    {
        let mut common = th.common.lock().unwrap();
        let result = &mut common.result.lock().unwrap();
        if result.score > pos.root_moves[0].score
            && (result.depth >= pos.completed_depth
                || result.score >= Value::MATE_IN_MAX_PLY)
        {
            pos.root_moves[0].score = result.score;
            pos.root_moves[0].pv = result.pv.clone();
        }
    }

    pos.previous_score = pos.root_moves[0].score;

    print!("bestmove {}", uci::move_str(pos.root_moves[0].pv[0],
        pos.is_chess960()));

    if pos.root_moves[0].pv.len() > 1 || extract_ponder_from_tt(pos) {
        print!(" ponder {}", uci::move_str(pos.root_moves[0].pv[1],
            pos.is_chess960()));
    }

    print!("\n");
    stdout().flush().unwrap();
}

// thread_search() is the main iterative deepening loop. It calls search()
// repeatedly with increasing depth until the allocated thinking time has
// been consumed, the user stops the search, or the maximum search depth
// is reached.

pub fn thread_search(pos: &mut Position, _th: &threads::ThreadCtrl) {
    let mut stack: Vec<Stack> = Vec::with_capacity((MAX_PLY + 7) as usize);

    let mut last_best_move = Move::NONE;
    let mut last_best_move_depth = Depth::ZERO;

    let mut time_reduction = 1.0f64;

    // only need to clear 0..7, but for now we do extra work
    for _ in 0..(MAX_PLY + 7) as usize {
        stack.push(Stack {
            pv: Vec::new(),
            cont_history: pos.cont_history.get(NO_PIECE, Square(0)),
            ply: 0,
            current_move: Move::NONE,
            excluded_move: Move::NONE,
            killers: [Move::NONE; 2],
            static_eval: Value::ZERO,
            stat_score: 0,
            move_count: 0,
        });
    }

    pos.calls_cnt = 0;
    pos.nmp_ply = 0;
    pos.nmp_odd = 0;

    let mut alpha = -Value::INFINITE;
    let mut delta = -Value::INFINITE;
    let mut best_value = -Value::INFINITE;
    let mut beta = Value::INFINITE;

    if pos.is_main {
        pos.failed_low = false;
        pos.best_move_changes = 0.0;
    }

    let mut multi_pv = ucioption::get_i32("MultiPV") as usize;
    multi_pv = std::cmp::min(multi_pv, pos.root_moves.len());

    let mut root_depth = Depth::ZERO;

    // Iterative deepening loop until requested to stop or the target depth
    // is reached
    while !threads::stop() {
        root_depth += ONE_PLY;
        if root_depth >= Depth::MAX
            || (limits().depth != 0
                && pos.is_main
                && root_depth / ONE_PLY > limits().depth as i32)
        {
            break;
        }

        // Distribute search depths across the threads
        if !pos.is_main {
            let i = ((pos.thread_idx - 1) & 20) as usize;
            if ((root_depth / ONE_PLY + pos.game_ply() + SKIP_PHASE[i]) /
                SKIP_SIZE[i]) % 2 != 0
            {
                continue;
            }
        }

        // Age out PV variability metric
        if pos.is_main {
            pos.best_move_changes *= 0.505;
            pos.failed_low = false;
        }

        // Save the last iteration's scores before first PV line is searched
        // and all the move scores except the (new) PV are set to
        // -Value::INFINITE.
        for ref mut rm in pos.root_moves.iter_mut() {
            rm.previous_score = rm.score;
        }

        let mut pv_first = 0;
        pos.pv_last = 0;

        // MultiPV loop. We perform a full root search for each PV line.
        pos.pv_idx = 0;
        while pos.pv_idx < multi_pv && !threads::stop() {
            if pos.pv_idx == pos.pv_last {
                pv_first = pos.pv_last;
                pos.pv_last += 1;
                while pos.pv_last < pos.root_moves.len() {
                    if pos.root_moves[pos.pv_last].tb_rank
                        != pos.root_moves[pv_first].tb_rank
                    {
                        break;
                    }
                    pos.pv_last += 1;
                }
            }

            // Reset UCI info sel_depth for each depth and each PV line
            pos.sel_depth = 0;

            // Skip the search if we have a mate value from DTM tables
            if pos.root_moves[pos.pv_idx].tb_rank.abs() > 1000 {
                best_value = pos.root_moves[pos.pv_idx].tb_score;
                pos.root_moves[pos.pv_idx].score = best_value;
                alpha = -Value::INFINITE;
                beta = Value::INFINITE;
                if pos.is_main
                    && (threads::stop()
                        || pos.pv_idx + 1 == multi_pv
                        || timeman::elapsed() > 3000)
                {
                    print_pv(pos, root_depth, alpha, beta);
                }
                pos.pv_idx += 1;
                continue;
            }

            // Reset aspiration window starting size
            if root_depth >= 5 * ONE_PLY {
                delta = Value(18);
                alpha = std::cmp::max(
                    pos.root_moves[pos.pv_idx].previous_score - delta,
                    -Value::INFINITE);
                beta = std::cmp::min(
                    pos.root_moves[pos.pv_idx].previous_score + delta,
                    Value::INFINITE);
            }

            // Start with a small aspiration window and, in the case of a fail
            // high/low, re-search with a bigger window until we're not failing
            // high/low anymore.
            loop {
                best_value = search::<Pv>(pos, &mut stack, alpha, beta,
                    root_depth, false, false);
                update_counters(pos);

                // Bring the best move to the front. It is critical that
                // sorting is done with a stable sort algorithm because all
                // the values but the first and eventually the new best one
                // are set to -Value::INFINITE and we want to keep the same
                // orer for all the mvoes except the new PV that goes to the
                // front. Note that in case of MultiPV search the PV lines
                // already searched are preserved.
                pos.root_moves[pos.pv_idx..].sort();

                // If search has been stopped, we break immediately. Sorting
                // and writing PV back to TT is safe because root_moves is
                // still valid, although it refers to the previous iteration.
                if threads::stop() {
                    break;
                }

                // When failing high/low give some update (without cluttering
                // the UI) before a re-search.
                if pos.is_main
                    && multi_pv == 1
                    && (best_value <= alpha || best_value >= beta)
                    && timeman::elapsed() > 3000
                {
                    print_pv(pos, root_depth, alpha, beta);
                }

                // In case of failing low/high increase aspiration window and
                // re-search, otherwise exit the loop.
                if best_value <= alpha {
                    beta = (alpha + beta) / 2;
                    alpha = std::cmp::max(best_value - delta, -Value::INFINITE);

                    if pos.is_main {
                        pos.failed_low = true;
                        threads::set_stop_on_ponderhit(false);
                    }
                } else if best_value >= beta {
                    beta = std::cmp::min(best_value + delta, Value::INFINITE);
                } else {
                    break;
                }

                delta += delta / 4 + 5;

                debug_assert!(alpha >= -Value::INFINITE
                    && beta <= Value::INFINITE);
            }

            // Sort the PV lines searched so far and update the GUI
            pos.root_moves[pv_first..pos.pv_idx+1].sort();

            if pos.is_main
                && (threads::stop() || pos.pv_idx + 1 == multi_pv
                    || timeman::elapsed() > 3000)
            {
                print_pv(pos, root_depth, alpha, beta);
            }

            pos.pv_idx += 1;
        }

        if !threads::stop() {
            pos.completed_depth = root_depth;
        }

        if pos.root_moves[0].pv[0] != last_best_move {
            last_best_move = pos.root_moves[0].pv[0];
            last_best_move_depth = root_depth;
        }

        // Have we found a "mate in x"?
        if limits().mate != 0
            && best_value >= Value::MATE_IN_MAX_PLY
            && (Value::MATE - best_value).0 <= 2 * (limits().mate as i32)
        {
            threads::set_stop(true);
        }

        if pos.is_main {
            continue;
        }

        // Do we have time for the next iteration? Can we stop searching now?
        if limits().use_time_management() {
            if !threads::stop() && !threads::stop_on_ponderhit() {
                // Stop the search if only one legal move is available or
                // if all of the available time has been used.
                let f = [ pos.failed_low as i32,
                          (best_value - pos.previous_score).0 ];
                let improving_factor = std::cmp::max(229,
                    std::cmp::min(715, 357 + 119 * f[0] - 6 * f[1]));

                let us = pos.side_to_move();
                let think_hard = best_value == Value::DRAW
                    && limits().time[us.0 as usize] - timeman::elapsed() >
                        limits().time[(!us).0 as usize]
                    && pv_is_draw(pos);
                let mut unstable_pv_factor = 1.0f64 + pos.best_move_changes
                    + (if think_hard { 1.0f64 } else { 0.0f64 });

                // if the best_move is stable over several iterations, reduce
                // time for this move, the longer the move has been stable,
                // the more. Use part of the gained time from a previous
                // stable move for the current move.
                time_reduction = 1.;
                for i in 3..6 {
                    if last_best_move_depth * i < pos.completed_depth
                        && !think_hard
                    {
                        time_reduction *= 1.3;
                    }
                    unstable_pv_factor *=
                        pos.previous_time_reduction.powf(0.51) / time_reduction;
                    if pos.root_moves.len() == 1
                        || (timeman::elapsed() as f64) >
                            (timeman::optimum() as f64) *
                            unstable_pv_factor *
                            (improving_factor as f64) / 628.0
                    {
                        // If we are allowed to ponder do not stop the search
                        // now but keep pondering until the GUI sends
                        // "ponderhit" or "stop".
                        if threads::ponder() {
                            threads::set_stop_on_ponderhit(true);
                        } else {
                            threads::set_stop(true);
                        }
                    }
                }
            }
        }

    }

    if pos.is_main {
        return;
    }

    pos.previous_time_reduction = time_reduction;
}

// search() is the main search function for both PV and non-PV nodes

fn search<NT: NodeType>(
    pos: &mut Position, ss: &mut [Stack], mut alpha: Value, mut beta: Value,
    depth: Depth, cut_node: bool, skip_early_pruning: bool
) -> Value {
    let nt = NT::node_type();
    let pv_node = nt == PV;
    let root_node = pv_node && ss[5].ply == 0;

    debug_assert!(-Value::INFINITE <= alpha && alpha < beta
        && beta <= Value::INFINITE);
    debug_assert!(pv_node || alpha == beta - 1);
    debug_assert!(Depth::ZERO < depth && depth < Depth::MAX);
    debug_assert!(!(pv_node && cut_node));
    debug_assert!(depth / ONE_PLY * ONE_PLY == depth);

    let mut captures_searched: [Move; 32] = [Move::NONE; 32];
    let mut quiets_searched: [Move; 64] = [Move::NONE; 64];

    // Step 1. Initialize node
    let in_check = pos.checkers() != 0;
    let mut move_count = 0;
    let mut capture_count = 0;
    let mut quiet_count = 0;
    ss[5].move_count = 0;
    ss[5].stat_score = 0;
    let mut best_value = -Value::INFINITE;
    let mut max_value = Value::INFINITE;

    // Check for the available remaining time
    pos.calls_cnt -= 1;
    if pos.calls_cnt < 0 {
        pos.calls_cnt = 4095;
        update_counters(pos);
        check_time();
    }

    // Used to send sel_depth info to GUI
    if pv_node && pos.sel_depth < ss[5].ply {
        pos.sel_depth = ss[5].ply;
    }

    if !root_node {
        // Step 2. Check for aborted search and immediate draw
        if threads::stop() || pos.is_draw(ss[5].ply) || ss[5].ply >= MAX_PLY {
            return if ss[5].ply >= MAX_PLY && !in_check { evaluate(pos) }
                   else { Value::DRAW };
        }

        // Step 3. Mate distance pruning. Even if we mate at the next move
        // our score would be at best mate_in(ss[5]->ply+1). If alpha is
        // already bigger because a shorter mate was found upward in the
        // tree then there is no need to search because we will never beat
        // the current alpha. Same logic but with reversed signs applies
        // in the opposite condition of being mated.
        alpha = std::cmp::max(mated_in(ss[5].ply), alpha);
        beta = std::cmp::min(mate_in(ss[5].ply+1), beta);
        if alpha >= beta {
            return alpha;
        }
    }

    debug_assert!(0 <= ss[5].ply && ss[5].ply < MAX_PLY);

    ss[6].ply = ss[5].ply + 1;
    ss[5].current_move = Move::NONE;
    ss[6].excluded_move = Move::NONE;
    let mut best_move = Move::NONE;
    ss[5].cont_history = pos.cont_history.get(NO_PIECE, Square(0));
    ss[7].killers = [Move::NONE; 2];
    let prev_sq = ss[4].current_move.to();

    // Step 4. Transposition table lookup. We don't want the score of a
    // partial search to overwrite a previous full search TT value, so we use
    // a different position key in case of an excluded move.
    let excluded_move = ss[5].excluded_move;
    let pos_key = pos.key() ^ Key((excluded_move.0 << 16) as u64);
    let (mut tte, mut tt_hit) = tt::probe(pos_key);
    let tt_value = if tt_hit { value_from_tt(tte.value(), ss[5].ply) }
                   else { Value::NONE };
    let mut tt_move = if root_node { pos.root_moves[pos.pv_idx].pv[0] }
                      else if tt_hit { tte.mov() } else { Move::NONE };

    // At non-PV nodes we check for an early cutoff
    if !pv_node
        && tt_hit
        && tte.depth() >= depth
        && tt_value != Value::NONE // Possible in case of TT access race
        && (if tt_value >= beta { tte.bound() & Bound::LOWER != 0 }
                           else { tte.bound() & Bound::UPPER != 0 })
    {
        // If tt_move is quiet, update move sorting heuristic on TT hit
        if tt_move != Move::NONE {
            if tt_value >= beta {
                if !pos.capture_or_promotion(tt_move) {
                    update_stats(pos, ss, tt_move, &quiets_searched, 0,
                        stat_bonus(depth));
                }

                // Extra penalty for a quiet TT in previous ply when it gets
                // refuted.
                if ss[4].move_count == 1 && pos.captured_piece() == NO_PIECE {
                    update_continuation_histories(ss, pos.piece_on(prev_sq),
                        prev_sq, -stat_bonus(depth + ONE_PLY));
                }
            }
            // Penalty for a quiet tt_move that fails low
            else if !pos.capture_or_promotion(tt_move) {
                let penalty = -stat_bonus(depth);
                pos.main_history.update(pos.side_to_move(), tt_move, penalty);
                update_continuation_histories(&ss[1..],
                    pos.moved_piece(tt_move), tt_move.to(), penalty);
            }
        }
        return tt_value;
    }

    // Step 4a. Tablebase probe
    if !root_node && tb::cardinality() != 0 {
        let pieces_cnt = popcount(pos.pieces());

        if pieces_cnt <= tb::cardinality()
            && (pieces_cnt < tb::cardinality() || depth >= tb::probe_depth())
            && pos.rule50_count() == 0
            && !pos.has_castling_right(ANY_CASTLING)
        {
            let mut found = 1;
            let wdl = tb::probe_wdl(pos, &mut found);

            if found != 0 {
                pos.tb_hits += 1;

                let draw_score = if tb::use_rule_50() { 1 } else { 0 };

                let value =
                    if wdl < -draw_score {
                        -Value::MATE + MAX_MATE_PLY + 1 + ss[5].ply
                    } else if wdl > draw_score {
                        Value::MATE - MAX_MATE_PLY - 1 - ss[5].ply
                    } else {
                        Value::DRAW + 2 * wdl * draw_score
                    };

                let b =
                    if wdl < -draw_score { Bound::UPPER }
                    else if wdl > draw_score { Bound::LOWER }
                    else { Bound::EXACT };

                if b == Bound::EXACT
                    || (if b == Bound::LOWER { value >= beta }
                        else { value <= alpha })
                {
                    tte.save(pos_key, value_to_tt(value, ss[5].ply), b,
                        std::cmp::min(Depth::MAX - ONE_PLY,
                            depth + 6 * ONE_PLY),
                        Move::NONE, Value::NONE, tt::generation());
                    return value;
                }

                if pieces_cnt <= tb::cardinality_dtm() {
                    let mut mate = tb::probe_dtm(pos, wdl, &mut found);
                    if found != 0 {
                        mate += if wdl > 0 { -ss[5].ply } else { ss[5].ply };
                        tte.save(pos_key, value_to_tt(mate, ss[5].ply),
                            Bound::EXACT, std::cmp::min(Depth::MAX - ONE_PLY,
                                depth + 6 * ONE_PLY),
                            Move::NONE, Value::NONE, tt::generation());
                        return mate;
                    }
                }

                if pv_node {
                    if b == Bound::LOWER {
                        best_value = value;
                        if best_value > alpha {
                            alpha = best_value;
                        }
                    } else {
                        max_value = value;
                    }
                }
            }
        }
    }

    // Step 5. Evaluate the position statically
    loop {
        let eval;
        if in_check {
            ss[5].static_eval = Value::NONE;
            break; // goto moves_loop;
        } else if tt_hit {
            // Never assume anything about values stored in TT
            let mut tmp = tte.eval();
            if tmp == Value::NONE {
                tmp = evaluate(pos);
            }
            ss[5].static_eval = tmp;

            // Can tt_value be used as a better position evaluation?
            if tt_value != Value::NONE
                && tte.bound()
                    & (if tt_value > tmp { Bound::LOWER } else { Bound::UPPER })
                        != 0
            {
                tmp = tt_value;
            }
            eval = tmp;
        } else {
            eval = if ss[4].current_move != Move::NULL { evaluate(pos) }
                   else { -ss[4].static_eval + 2 * evaluate::TEMPO };
            ss[5].static_eval = eval;
            tte.save(pos_key, Value::NONE, Bound::NONE, Depth::NONE,
                Move::NONE, eval, tt::generation());
        }

        if skip_early_pruning
            || pos.non_pawn_material_c(pos.side_to_move()) == Value::ZERO
        {
            break; // goto moves_loop;
        }

        // Step 6. Razoring (skipped when in check)
        if !pv_node
            && depth < 4 * ONE_PLY
            && eval + razor_margin() <= alpha
        {
            if depth <= ONE_PLY {
                return qsearch::<NonPv, False>(pos, ss, alpha, alpha+1,
                    Depth::ZERO);
            }

            let ralpha = alpha - razor_margin();
            let v = qsearch::<NonPv, False>(pos, ss, ralpha, ralpha+1,
                Depth::ZERO);
            if v <= ralpha {
                return v;
            }
        }

        // Step 7. Futility pruning: child node (skipped when in check)
        if !root_node
            && depth < 7 * ONE_PLY
            && eval - futility_margin(depth) >= beta
            && eval < Value::KNOWN_WIN
        {
            return eval;
        }

        // Step 8. Null move search with verification search (ommitted in PV
        // nodes)
        if !pv_node
            && eval >= beta
            && ss[5].static_eval >= beta - 36 * depth / ONE_PLY + 225
            && (ss[5].ply >= pos.nmp_ply || ss[5].ply & 1 != pos.nmp_odd)
        {
            debug_assert!(eval - beta >= Value::ZERO);

            // Null move dynamic reduction based on depth and value
            let r = ((823 + 67 * depth / ONE_PLY) / 256
                + std::cmp::min((eval - beta) / PawnValueMg, 3)) * ONE_PLY;

            ss[5].current_move = Move::NULL;
            ss[5].cont_history = pos.cont_history.get(NO_PIECE, Square(0));

            pos.do_null_move();
            let mut null_value = if depth-r < ONE_PLY {
                -qsearch::<NonPv, False>(pos, &mut ss[1..], -beta, -beta+1,
                    Depth::ZERO)
            } else {
                -search::<NonPv>(pos, &mut ss[1..], -beta, -beta+1, depth-r,
                    !cut_node, true)
            };
            pos.undo_null_move();

            if null_value >= beta {
                // Do not return unproven mate scores
                if null_value >= Value::MATE_IN_MAX_PLY {
                    null_value = beta;
                }

                if (depth < 12 * ONE_PLY || pos.nmp_ply != 0)
                    && beta.abs() < Value::KNOWN_WIN
                {
                    return null_value;
                }

                // Do verification search at high depths
                // Disable null move pruning for the side to move for the
                // first part of the remaining search tree
                pos.nmp_ply = ss[5].ply + 3 * (depth-r) / (4 * ONE_PLY);
                pos.nmp_odd = ss[5].ply & 1;
                let v = if depth-r < ONE_PLY {
                    qsearch::<NonPv, False>(pos, ss, beta-1, beta, Depth::ZERO)
                } else {
                    search::<NonPv>(pos, ss, beta-1, beta, depth-r, false, true)
                };
                pos.nmp_odd = 0;
                pos.nmp_ply = 0;
                if v >= beta {
                    return null_value;
                }
            }
        }

        // Step 9. ProbCut (skipped when in check)
        // If we have a good enough capture and a reduced search returns a
        // value much above beta, we can (almost) safely prune the previous
        // move.
        if !pv_node
            && depth >= 5 * ONE_PLY
            && beta.abs() < Value::MATE_IN_MAX_PLY
        {
            let rbeta = std::cmp::min(beta + 200, Value::INFINITE);

            debug_assert!(ss[4].current_move.is_ok());

            let mut mp =
                MovePickerPC::new(pos, tt_move, rbeta - ss[5].static_eval);
            loop {
                let m = mp.next_move(pos);
                if m == Move::NONE {
                    break;
                }
                if pos.legal(m) {
                    ss[5].current_move = m;
                    ss[5].cont_history =
                        pos.cont_history.get(pos.moved_piece(m), m.to());
                    debug_assert!(depth >= 5 * ONE_PLY);
                    let gives_check = pos.gives_check(m);
                    pos.do_move(m, gives_check);
                    let value = -search::<NonPv>(pos, &mut ss[1..], -rbeta,
                        -rbeta+1, depth - 4 * ONE_PLY, !cut_node, false);
                    pos.undo_move(m);
                    if value >= rbeta {
                        return value;
                    }
                }
            }
        }

        // Step 10. Internal iterative deepening (skipped when in check)
        if depth >= 6 * ONE_PLY
            && tt_move == Move::NONE
            && (pv_node || ss[5].static_eval + 256 >= beta)
        {
            let d = (3 * depth / (4 * ONE_PLY) - 2) * ONE_PLY;
            search::<NT>(pos, ss, alpha, beta, d, cut_node, true);

            let (tmp_tte, tmp_tt_hit) = tt::probe(pos_key);
            tte = tmp_tte;
            tt_hit = tmp_tt_hit;
            tt_move = if tt_hit { tte.mov() } else { Move::NONE };
        }

        break;
    }

    // When in check search starts from here ("moves_loop")

    let cont_hist =
        (ss[4].cont_history, ss[3].cont_history, ss[1].cont_history);

    let mut mp = MovePicker::new(pos, tt_move, depth, ss);
    let mut value = best_value;

    let improving = ss[5].static_eval >= ss[3].static_eval
                    || ss[3].static_eval == Value::NONE;

    let singular_extension_node =
        !root_node
        && depth >= 8 * ONE_PLY
        && tt_move != Move::NONE
        && tt_value != Value::NONE
        && excluded_move == Move::NONE
        && tte.bound() & Bound::LOWER != 0
        && tte.depth() >= depth - 3 * ONE_PLY;

    let mut skip_quiets = false;
    let mut tt_capture = false;
    let pv_exact = pv_node && tt_hit && tte.bound() == Bound::EXACT;

    // Step 11. Loop through moves
    // Loop through all pseudo-legal moves until no moves remain or a beta
    // cutoff occurs
    loop {
        let m = mp.next_move(pos, skip_quiets);
        if m == Move::NONE {
            break;
        }

        debug_assert!(m.is_ok());

        if m == excluded_move {
            continue;
        }

        // At root obey the "searchmoves" option and skip moves not listed in
        // root_moves. As a consequence, any illegal move is also skipped.
        // In MultiPV mode we also skip PV moves which have already been
        // searched.
        if root_node
            && !pos.root_moves[pos.pv_idx..].iter().any(|ref rm| rm.pv[0] == m)
        {
            continue;
        }

        move_count += 1;
        ss[5].move_count = move_count;

        if root_node && pos.is_main && timeman::elapsed() > 3000 {
            println!( "info depth {} currmove {} currmovenumber {}",
                depth / ONE_PLY, uci::move_str(m, pos.is_chess960()),
                move_count + pos.pv_idx as i32
            );
            stdout().flush().unwrap();
        }

        if pv_node {
            ss[6].pv.truncate(0);
        }

        let mut extension = Depth::ZERO;
        let capture_or_promotion = pos.capture_or_promotion(m);
        let moved_piece = pos.moved_piece(m);

        let gives_check =
            if m.move_type() == NORMAL
                && pos.discovered_check_candidates() == 0
            {
                pos.check_squares(moved_piece.piece_type()) & m.to() != 0
            } else {
                pos.gives_check(m)
            };

        let move_count_pruning =
            depth < 16 *ONE_PLY
            && move_count >= futility_move_counts(improving, depth);

        // Step 12. Singular and Gives Check Extensions

        // Singular extension search. If all moves but one fail low on a search
        // of (alpha-s, beta-s), and just one fails high on (alpha, beta), then
        // that is singular and should be extended. To verify this, we do a
        // reduced search on all moves but the tt_move and if the result is
        // lower than tt_value minus a margin, we will extend the tt_move.
        if singular_extension_node
            && m == tt_move
            && pos.legal(m)
        {
            let rbeta =
                std::cmp::max(tt_value - 2 * depth / ONE_PLY, -Value::MATE);
            let d = (depth / (2 * ONE_PLY)) * ONE_PLY;
            ss[5].excluded_move = m;
            let value = search::<NonPv>(pos, ss, rbeta - 1, rbeta, d, cut_node,
                true);
            ss[5].excluded_move = Move::NONE;

            if value < rbeta {
                extension = ONE_PLY;
            }
        } else if gives_check
                    && !move_count_pruning
                    && pos.see_ge(m, Value::ZERO)
        {
            extension = ONE_PLY;
        }

        // Calculate new depth for this move
        let new_depth = depth - ONE_PLY + extension;

        // Step 13. Pruning at shallow depth
        if !root_node
            && pos.non_pawn_material_c(pos.side_to_move()) != Value::ZERO
            && best_value > Value::MATED_IN_MAX_PLY
        {
            if !capture_or_promotion
                && !gives_check
                && (!pos.advanced_pawn_push(m)
                    || pos.non_pawn_material() >= Value(5000))
            {
                // Move count based pruning
                if move_count_pruning {
                    skip_quiets = true;
                    continue;
                }

                // Reduced depth of the next LMR search
                let lmr_depth = std::cmp::max(
                    new_depth - reduction::<NT>(improving, depth, move_count),
                    Depth::ZERO) / ONE_PLY;

                // Countermoves based pruning
                if lmr_depth < 3
                    && cont_hist.0.get(moved_piece, m.to()) < CM_THRESHOLD
                    && cont_hist.1.get(moved_piece, m.to()) < CM_THRESHOLD
                {
                    continue;
                }

                // Futility pruning: parent node
                if lmr_depth < 7
                    && !in_check
                    && ss[5].static_eval + 256 + 200 * lmr_depth <= alpha
                {
                    continue;
                }

                // Prune moves with negative SEE
                if lmr_depth < 8
                    && !pos.see_ge(m, Value(-35 * lmr_depth * lmr_depth))
                {
                    continue;
                }
            } else if depth < 7 * ONE_PLY
                && extension == Depth::ZERO
                && !pos.see_ge(m, -PawnValueEg * (depth / ONE_PLY))
            {
                continue;
            }
        }

        // prefetch

        // Check for legality just before making the move
        if !root_node && !pos.legal(m) {
            move_count -= 1;
            ss[5].move_count = move_count;
            continue;
        }

        if m == tt_move && capture_or_promotion {
            tt_capture = true;
        }

        // Update the current move (this must be done after singular extension
        // search)
        ss[5].current_move = m;
        ss[5].cont_history = pos.cont_history.get(moved_piece, m.to());

        // Step 14. Make the move
        pos.do_move(m, gives_check);

        // Step 15. Reduced depth search (LMR). If the move fails high it will
        // be re-searched at full depth.
        let do_full_depth_search;

        if depth >= 3 * ONE_PLY
            && move_count > 1
            && (!capture_or_promotion || move_count_pruning)
        {
            let mut r = reduction::<NT>(improving, depth, move_count);

            if capture_or_promotion {
                r -= if r != Depth::ZERO { ONE_PLY } else { Depth::ZERO };
            } else {

                // Decrease reduction if opponent's move count is high
                if ss[4].move_count > 15 {
                    r -= ONE_PLY;
                }

                // Decrease reduction for exact PV nodes
                if pv_exact {
                    r -= ONE_PLY;
                }

                // Increase reduction if tt_move is a capture
                if tt_capture {
                    r += ONE_PLY;
                }

                // Increase reduction for cut nodes
                if cut_node {
                    r += 2 * ONE_PLY;
                }

                // Decrease reduction for moves that escape a capture. Filter
                // out castling moves, because they are coded as "king captures
                // rook" and hence break do_move().
                else if m.move_type() == NORMAL
                    && !pos.see_ge(Move::make(m.to(), m.from()), Value::ZERO)
                {
                    r -= 2 * ONE_PLY;
                }

                ss[5].stat_score =
                    pos.main_history.get(!pos.side_to_move(), m)
                    + cont_hist.0.get(moved_piece, m.to())
                    + cont_hist.1.get(moved_piece, m.to())
                    + cont_hist.2.get(moved_piece, m.to())
                    - 4000; // Correction factor

                // Decrease/increase reduction by comparing opponent's stat
                // score
                if ss[5].stat_score >= 0 && ss[4].stat_score < 0 {
                    r -= ONE_PLY;
                } else if ss[4].stat_score >= 0 && ss[5].stat_score < 0 {
                    r += ONE_PLY;
                }

                // Decrease/increase reduction for moves with a good/bad
                // history
                r = std::cmp::max(Depth::ZERO,
                    (r / ONE_PLY - ss[5].stat_score / 20000) * ONE_PLY);
            }

            let d = std::cmp::max(new_depth - r, ONE_PLY);

            value = -search::<NonPv>(pos, &mut ss[1..], -(alpha+1), -alpha, d,
                true, false);
            do_full_depth_search = value > alpha && d != new_depth;
        } else {
            do_full_depth_search = !pv_node || move_count > 1;
        }

        // Step 16. Full depth search if LMR is skipped or fails high
        if do_full_depth_search {
            value =
                if new_depth < ONE_PLY {
                    if gives_check {
                        -qsearch::<NonPv, True>(pos, &mut ss[1..], -(alpha+1),
                            -alpha, Depth::ZERO)
                    } else {
                        -qsearch::<NonPv, False>(pos, &mut ss[1..], -(alpha+1),
                            -alpha, Depth::ZERO)
                    }
                } else {
                    -search::<NonPv>(pos, &mut ss[1..], -(alpha+1), -alpha,
                        new_depth, !cut_node, false)
                };
        }

        // For PV nodes only, do a full PV search on the first move or after a
        // fail high (in the latter case search only if value < beta),
        // otherwise let the parent node fail low with value <= alpha and try
        // another move.
        if pv_node
            && (move_count == 1
                || (value > alpha && (root_node || value < beta)))
        {
            ss[6].pv.truncate(0);

            value =
                if new_depth < ONE_PLY {
                    if gives_check {
                        -qsearch::<Pv, True>(pos, &mut ss[1..], -beta, -alpha,
                            Depth::ZERO)
                    } else {
                        -qsearch::<Pv, False>(pos, &mut ss[1..], -beta, -alpha,
                            Depth::ZERO)
                    }
                } else {
                    -search::<Pv>(pos, &mut ss[1..], -beta, -alpha, new_depth,
                        false, false)
                };
        }

        // Step 17. Undo move
        pos.undo_move(m);

        debug_assert!(value > -Value::INFINITE && value < Value::INFINITE);

        // Step 18. Check for a new best move
        // Finished searching the move. If a stop occurred, the return value
        // of the search cannot be trusted, and we return immediately without
        // updating best move, PV and TT.
        if threads::stop() {
            return Value::ZERO;
        }

        if root_node {
            let rm = pos.root_moves
                .iter_mut()
                .find(|ref rm| rm.pv[0] == m).unwrap();

            // PV move or new best move?
            if move_count == 1 || value > alpha {
                rm.score = value;
                rm.sel_depth = pos.sel_depth;
                rm.pv.truncate(1);

                for &m in ss[6].pv.iter() {
                    rm.pv.push(m);
                }

                // We record how often the best move changes in each iteration.
                // This information is used for time management: if the best
                // move changes frequently, we allocate some more time.
                if move_count > 1 && pos.is_main {
                    pos.best_move_changes += 1.0;
                }
            } else {
                // All other moves but the PV are set to the lowest value: this
                // is not a problem when sorting because the sort is stable and
                // the move position in the list is preserved - just the PV is
                // pushed up.
                rm.score = -Value::INFINITE;
            }
        }

        if value > best_value {
            best_value = value;

            if value > alpha {
                best_move = m;

                if pv_node && !root_node { // Update pv even in fail-high case
                    update_pv(ss, m);
                }

                if pv_node && value < beta { // Update alpha
                    alpha = value;
                } else {
                    debug_assert!(value >= beta); // Fail high
                    break;
                }
            }
        }

        if !capture_or_promotion && m != best_move && quiet_count < 64 {
            quiets_searched[quiet_count] = m;
            quiet_count += 1;
        } else if capture_or_promotion && m != best_move && capture_count < 32 {
            captures_searched[capture_count] = m;
            capture_count += 1;
        }
    }

    // Step 20. Check for mate and stalemante
    // All legal mvoes have been searched and if there are no legal moves, it
    // must be a mate or a stalemate. If we are in a singular extension search,
    // then return a fail low score.

    if move_count == 0 {
        best_value =
            if excluded_move != Move::NONE { alpha }
            else if in_check { mated_in(ss[5].ply) }
            else { Value::DRAW };
    } else if best_move != Move::NONE {
        // Quiet best move: update move sorting heuristics
        if !pos.capture_or_promotion(best_move) {
            update_stats(pos, ss, best_move, &quiets_searched, quiet_count,
                stat_bonus(depth));
        } else {
            update_capture_stats(pos, best_move, &captures_searched,
                capture_count, stat_bonus(depth));
        }

        // Extra penalty for a quiet TT move in previous ply if it gets
        // refuted
        if ss[4].move_count == 1 && pos.captured_piece() == NO_PIECE {
            update_continuation_histories(ss, pos.piece_on(prev_sq), prev_sq,
                -stat_bonus(depth + ONE_PLY));
        }
    }
    // Bonus for prior countermove that caused the fail low
    else if depth >= 3 * ONE_PLY
                && pos.captured_piece() == NO_PIECE
                && ss[4].current_move.is_ok()
    {
        update_continuation_histories(ss, pos.piece_on(prev_sq), prev_sq,
            stat_bonus(depth));
    }

    if pv_node && best_value > max_value {
        best_value = max_value;
    }

    if excluded_move == Move::NONE {
        tte.save(pos_key, value_to_tt(best_value, ss[5].ply),
            if best_value >= beta { Bound::LOWER }
            else if pv_node && best_move != Move::NONE { Bound::EXACT }
            else { Bound::UPPER },
            depth, best_move, ss[5].static_eval, tt::generation());
    }

    debug_assert!(best_value > -Value::INFINITE
        && best_value < Value::INFINITE);

    return best_value;
}

// qsearch() is the quiescence search function, which is called by the main
// search function with depth zero or recursively with depth less than ONE_PLY.

fn qsearch<NT: NodeType, InCheck: Bool> (
    pos: &mut Position, ss: &mut [Stack], mut alpha: Value, beta: Value,
    depth: Depth
) -> Value {
    let nt = NT::node_type();
    let in_check = InCheck::bool();
    let pv_node = nt == PV;

    debug_assert!(in_check == (pos.checkers() != 0));
    debug_assert!(alpha >= -Value::INFINITE
        && alpha < beta && beta <= Value::INFINITE);
    debug_assert!(pv_node || (alpha == beta - 1));
    debug_assert!(depth <= Depth::ZERO);
    debug_assert!(depth / ONE_PLY * ONE_PLY == depth);

    let old_alpha = alpha;
    if pv_node {
        ss[5].pv.truncate(0);
    }

    ss[5].current_move = Move::NONE;
    let mut best_move = Move::NONE;
    ss[6].ply = ss[5].ply + 1;
    let mut move_count = 0;

    // Check for an instant draw or if maximum ply count has been reached
    if pos.is_draw(ss[5].ply) || ss[5].ply >= MAX_PLY {
        return if ss[5].ply >= MAX_PLY && !in_check { evaluate(pos) }
               else { Value::DRAW };
    }

    debug_assert!(0 <= ss[5].ply && ss[5].ply < MAX_PLY);

    // Decide whether or not to include checks: this fixes also the type of
    // TT entry depth that we are going to use. Note that in qsearch we use
    // only two types of depth in TT: DEPTH_QS_CHECKS or DEPTH_QS_NO_CHECKS.
    let tt_depth =
        if in_check || depth >= Depth::QS_CHECKS { Depth::QS_CHECKS }
        else { Depth::QS_NO_CHECKS };
    // Transposition table lookup
    let pos_key = pos.key();
    let (tte, tt_hit) = tt::probe(pos_key);
    let tt_move = if tt_hit { tte.mov() } else { Move::NONE };
    let tt_value = if tt_hit {
        value_from_tt(tte.value(), ss[5].ply)
    } else {
        Value::NONE
    };

    if !pv_node
        && tt_hit
        && tte.depth() >= tt_depth
        && tt_value != Value::NONE // Only in case of TT access race
        && (if tt_value >= beta { tte.bound() & Bound::LOWER != 0 }
                           else { tte.bound() & Bound::UPPER != 0 })
    {
        return tt_value;
    }

    let mut best_value;
    let futility_base;

    // Evaluate the position statically
    if in_check {
        ss[5].static_eval = Value::NONE;
        best_value = -Value::INFINITE;
        futility_base = -Value::INFINITE;
    } else {
        if tt_hit {
            // Never assume anything on values stored in TT
            let mut tmp = tte.eval();
            if tmp == Value::NONE {
                tmp = evaluate(pos);
            }
            ss[5].static_eval = tmp;
            // Can tt_value be used as a better evaluation?
            if tt_value != Value::NONE
                && tte.bound()
                    & (if tt_value > tmp { Bound::LOWER } else { Bound::UPPER })
                        != 0
            {
                best_value = tt_value;
            } else {
                best_value = tmp;
            }
        } else {
            best_value =
                if ss[4].current_move != Move::NULL {
                    evaluate(pos)
                } else {
                    -ss[4].static_eval + 2 * evaluate::TEMPO
                };
            ss[5].static_eval = best_value;
        }

        // Stand pat. Return immediately if static value is at least beta
        if best_value >= beta {
            if !tt_hit {
                tte.save(pos.key(), value_to_tt(best_value, ss[5].ply),
                    Bound::LOWER, Depth::NONE, Move::NONE, ss[5].static_eval,
                    tt::generation());
            }

            return best_value;
        }

        if pv_node && best_value > alpha {
            alpha = best_value;
        }

        futility_base = best_value + 128;
    }

    // Initialize a MovePicker object for the current position and prepare to
    // search the moves. Because the depth is <= 0 here, only captures, queen
    // promotions and checks (only if depth >= DEPTH_QS_CHECKS) will be
    // generated.
    let mut mp = MovePickerQ::new(pos, tt_move, depth, ss[4].current_move.to());

    loop {
        let m = mp.next_move(pos);
        if m == Move::NONE {
            break;
        }

        debug_assert!(m.is_ok());

        let gives_check =
            if m.move_type() == NORMAL
                && pos.discovered_check_candidates() == 0
            {
                pos.check_squares(pos.moved_piece(m).piece_type())
                & m.to() != 0
            } else {
                pos.gives_check(m)
            };

        move_count += 1;

        if !in_check
            && !gives_check
            && futility_base > -Value::KNOWN_WIN
            && !pos.advanced_pawn_push(m)
        {
            debug_assert!(m.move_type() != ENPASSANT);

            let futility_value =
                futility_base + piece_value(EG, pos.piece_on(m.to()));

            if futility_value <= alpha {
                best_value = std::cmp::max(best_value, futility_value);
                continue;
            }

            if futility_base <= alpha && !pos.see_ge(m, Value::ZERO + 1)
            {
                best_value = std::cmp::max(best_value, futility_base);
                continue;
            }
        }

        // Detect non-capture evasions that are candidates to be pruned
        let evasion_prunable =
            in_check
            && (depth != Depth::ZERO || move_count > 2)
            && best_value > Value::MATED_IN_MAX_PLY
            && !pos.capture(m);

        if (!in_check || evasion_prunable)
            && !pos.see_ge(m, Value::ZERO)
        {
            continue;
        }

        // prefetch

        if !pos.legal(m) {
            move_count -= 1;
            continue;
        }

        ss[5].current_move = m;

        // Make and search the move
        pos.do_move(m, gives_check);
        let value = if gives_check {
            -qsearch::<NT, True>(pos, &mut ss[1..], -beta, -alpha,
                depth - ONE_PLY)
        } else {
            -qsearch::<NT, False>(pos, &mut ss[1..], -beta, -alpha,
                depth - ONE_PLY)
        };
        pos.undo_move(m);

        debug_assert!(value > -Value::INFINITE && value < Value::INFINITE);

        // Check for a new best move
        if value > best_value {
            best_value = value;

            if value > alpha {
                if pv_node { // Update pv even in fail-high case
                    update_pv(ss, m);
                }

                if pv_node && value < beta { // Update alpha here!
                    alpha = value;
                    best_move = m;
                } else { // fail high
                    tte.save(pos_key, value_to_tt(value, ss[5].ply),
                        Bound::LOWER, tt_depth, m, ss[5].static_eval,
                        tt::generation());

                    return value;
                }
            }
        }
    }

    // All legal moves have been searched. A special case: If we're in check
    // and no legal moves were found, it is checkmate.
    if in_check && best_value == -Value::INFINITE {
        return mated_in(ss[5].ply); // Plies to mate from the root
    }

    tte.save(pos_key, value_to_tt(best_value, ss[5].ply),
        if pv_node && best_value > old_alpha { Bound::EXACT }
        else { Bound::UPPER },
        tt_depth, best_move, ss[5].static_eval, tt::generation());

    debug_assert!(
        best_value > -Value::INFINITE && best_value < Value::INFINITE
    );

    return best_value;
}

// value_to_tt() adjusts a mate score from "plies to mate from the root" to
// "plies to mate from the current position". Non-mate scores are unchanged.
// The function is called before storing a value in the transposition table.

fn value_to_tt(v: Value, ply: i32) -> Value {
    debug_assert!(v != Value::NONE);

    if v >= Value::MATE_IN_MAX_PLY {
        v + ply
    } else if v <= Value::MATED_IN_MAX_PLY {
        v - ply
    } else {
        v
    }
}

// value_from_tt() is the inverse of value_to_tt(). It adjusts a mate score
// from the transposition table (which refers to the plies to mate/be mated
// from current position) to "plies to mate/be mated from the root".

fn value_from_tt(v: Value, ply: i32) -> Value {
    if v == Value::NONE {
        Value::NONE
    } else if v >= Value::MATE_IN_MAX_PLY {
        v - ply
    } else if v <= Value::MATED_IN_MAX_PLY {
        v + ply
    } else {
        v
    }
}

// update_pv() adds current move and appends child pv

fn update_pv(ss: &mut [Stack], m: Move) {
    ss[5].pv.truncate(0);
    ss[5].pv.push(m);
    for i in 0..ss[6].pv.len() {
        let m = ss[6].pv[i];
        ss[5].pv.push(m);
    }
}

// update_continuation_histories() updates histories of the move pairs formed
// by moves at ply -1, -2 and -4 with current move.

fn update_continuation_histories(
    ss: &[Stack], pc: Piece, to: Square, bonus: i32
) {
    if ss[3].current_move.is_ok() {
        ss[3].cont_history.update(pc, to, bonus);
    }
    if ss[2].current_move.is_ok() {
        ss[2].cont_history.update(pc, to, bonus);
    }
    if ss[0].current_move.is_ok() {
        ss[0].cont_history.update(pc, to, bonus);
    }
}

// update_capture_stats() updates move sorting heuristics when a new capture
// best move is found.

fn update_capture_stats(
    pos: &Position, m: Move, captures: &[Move], capture_cnt: usize, bonus: i32
) {
    let capture_history = &pos.capture_history;
    let moved_piece = pos.moved_piece(m);
    let captured = pos.piece_on(m.to()).piece_type();
    capture_history.update(moved_piece, m.to(), captured, bonus);

    // Decrease all the other played capture moves
    for i in 0..capture_cnt {
        let moved_piece = pos.moved_piece(captures[i]);
        let captured = pos.piece_on(captures[i].to()).piece_type();
        capture_history.update(moved_piece, captures[i].to(), captured, -bonus);
    }
}

// update_stats() updates move sorting heuristics when a new quiet best move
// is found

fn update_stats(
    pos: &Position, ss: &mut [Stack], m: Move, quiets: &[Move],
    quiets_cnt: usize, bonus: i32
) {
    if ss[5].killers[0] != m {
        ss[5].killers[1] = ss[5].killers[0];
        ss[5].killers[0] = m;
    }

    let c = pos.side_to_move();
    pos.main_history.update(c, m, bonus);
    update_continuation_histories(&ss[1..], pos.moved_piece(m), m.to(), bonus);

    if ss[4].current_move.is_ok() {
        let prev_sq = ss[4].current_move.to();
        pos.counter_moves.set(pos.piece_on(prev_sq), prev_sq, m);
    }

    // Decrease all the other played quiet moves
    for i in 0..quiets_cnt {
        pos.main_history.update(c, quiets[i], -bonus);
        update_continuation_histories(&ss[1..], pos.moved_piece(quiets[i]),
            quiets[i].to(), -bonus);
    }
}

// Is the PV leading to a draw position?
fn pv_is_draw(pos: &mut Position) -> bool {
    let pv_len = pos.root_moves[0].pv.len();

    for i in 0..pv_len {
        let m = pos.root_moves[0].pv[i];
        let gives_check = pos.gives_check(m);
        pos.do_move(m, gives_check);
    }

    let is_draw = pos.is_draw(pv_len as i32);

    for i in (0..pv_len).rev() {
        let m = pos.root_moves[0].pv[i];
        pos.undo_move(m);
    }

    is_draw
}

fn update_counters(pos: &Position) {
    let th = pos.thread_ctrl.as_ref().unwrap();
    th.nodes.set(pos.nodes);
    th.tb_hits.set(pos.tb_hits);
}

// check_time() is used to print debug info and, more importantly, to detect
// when we are out of available time and have to stop the search.

fn check_time() {
    // An engine may not stop pondering until told so by the GUI
    if threads::ponder() {
        return;
    }

    let elapsed = timeman::elapsed();

    if (limits().use_time_management() && elapsed > timeman::maximum() - 10)
        || (limits().movetime != 0 && elapsed >= limits().movetime)
        || (limits().nodes != 0 && threads::nodes_searched() >= limits().nodes)
    {
        threads::set_stop(true);
    }
}

// print_pv() prints PV information according to the UCI protocol. UCI
// requires that all (if any) unsearched PV lines are sent using a previous
// search score.

fn print_pv(pos: &mut Position, depth: Depth, alpha: Value, beta: Value) {
    let elapsed = timeman::elapsed() + 1;
    let pv_idx = pos.pv_idx;
    let multi_pv = std::cmp::min(ucioption::get_i32("MultiPV") as usize,
        pos.root_moves.len());
    let nodes_searched = threads::nodes_searched();
    let tb_hits = threads::tb_hits();

    for i in 0..multi_pv {
        let updated = i <= pv_idx
            && pos.root_moves[i].score != -Value::INFINITE;

        if depth == ONE_PLY && !updated {
            continue;
        }

        let d = if updated { depth } else { depth - ONE_PLY };
        let mut v = if updated { pos.root_moves[i].score}
            else { pos.root_moves[i].previous_score };

        let tb = tb::root_in_tb() && v.abs() < Value::MATE - MAX_MATE_PLY;
        if tb {
            v = pos.root_moves[i].tb_score;
        }

        // An incomplete mate PV may be caused by cutoffs in qsearch() and
        // by TB cutoffs. We try to complete the mate PV if we may be in the
        // latter case.
        if v.abs() > Value::MATE - MAX_MATE_PLY
            && (pos.root_moves[i].pv.len() as i32) < (Value::MATE - v.abs()).0
            && tb::cardinality_dtm() > 0
        {
            tb::expand_mate(pos, i);
        }

        print!("info depth {} seldepth {} multipv {} score {} ",
            d / ONE_PLY, pos.root_moves[i].sel_depth + 1, i + 1, uci::value(v));

        if !tb && i == pv_idx {
            if v >= beta {
                print!("lowerbound ");
            } else if v <= alpha {
                print!("upperbound ");
            }
        }

        print!("nodes {} nps {}",
            nodes_searched, nodes_searched * 1000 / (elapsed as u64));

        if elapsed > 1000 {
            print!(" hashfull {}", tt::hashfull());
        }

        print!(" tbhits {} time {} pv", tb_hits, elapsed);

        for &m in pos.root_moves[i].pv.iter() {
            print!(" {}", uci::move_str(m, pos.is_chess960()));
        }
        println!("");
    }
    stdout().flush().unwrap();
}

// extract_ponder_from_tt() is called in case we have no ponder move before
// exiting the search, for instance in case we stop the search during a fail
// high at root. We try hard to have a ponder move to return to the GUI,
// otherwise in case of 'ponder on' we have nothing to think on.

fn extract_ponder_from_tt(pos: &mut Position) -> bool {
    debug_assert!(pos.root_moves[0].pv.len() == 1);

    let m1 = pos.root_moves[0].pv[0];

    if m1 == Move::NONE {
        return false;
    }

    let gives_check = pos.gives_check(m1);
    pos.do_move(m1, gives_check);
    let (tte, tt_hit) = tt::probe(pos.key());

    if tt_hit {
        let m2 = tte.mov(); // Local copy to be SMP safe.
        if MoveList::new::<Legal>(pos).contains(m2) {
            pos.root_moves[0].pv.push(m2);
        }
    }

    pos.undo_move(m1);
    return pos.root_moves[0].pv.len() > 1;
}
