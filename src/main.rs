// SPDX-License-Identifier: GPL-3.0-or-later

extern crate memmap;

mod benchmark;
mod bitbases;
#[macro_use]
mod bitboard;
mod endgame;
mod evaluate;
mod material;
mod misc;
mod movegen;
mod movepick;
mod pawns;
mod position;
mod psqt;
mod search;
mod tb;
mod threads;
mod timeman;
mod tt;
mod types;
mod uci;
mod ucioption;

use std::thread;

fn main() {
    println!("{}", misc::engine_info(false));

    ucioption::init();
    psqt::init();
    bitboard::init();
    position::zobrist::init();
    bitbases::init();
    search::init();
    pawns::init();
    endgame::init();
    tt::resize(ucioption::get_i32("Hash") as usize);
    threads::init(ucioption::get_i32("Threads") as usize);
    tb::init(ucioption::get_string("SyzygyPath"));
    search::clear();

    // To avoid a stack overflow, we create a thread with a large
    // enough stack size to run the UI.
    let builder = thread::Builder::new().stack_size(16 * 1024 * 1024);
    let ui_thread = builder.spawn(|| uci::cmd_loop()).unwrap();
    let _ = ui_thread.join();
    // uci::cmd_loop();

    threads::free();
    tb::free();
    tt::free();
    ucioption::free();
}
