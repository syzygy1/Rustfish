// SPDX-License-Identifier: GPL-3.0-or-later

use tb;
use threads;
use tt;

use std;

type OnChange = Option<fn(&OptVal)>;

struct Opt {
    key: &'static str,
    val: OptVal,
    on_change: OnChange,
}

impl Opt {
    pub fn new(key: &'static str, val: OptVal, on_change: OnChange) -> Opt {
        Opt {
            key: key,
            val: val,
            on_change: on_change,
        }
    }
}

enum OptVal {
    StringOpt {
        def: &'static str,
        cur: String,
    },
    Spin {
        def: i32,
        cur: i32,
        min: i32,
        max: i32,
    },
    Check {
        def: bool,
        cur: bool,
    },
    Button,
}

impl OptVal {
    pub fn string(def: &'static str) -> OptVal {
        OptVal::StringOpt {
            def: def,
            cur: String::from(def),
        }
    }

    pub fn spin(def: i32, min: i32, max: i32) -> OptVal {
        OptVal::Spin {
            def: def,
            cur: def,
            min: min,
            max: max,
        }
    }

    pub fn check(def: bool) -> OptVal {
        OptVal::Check {
            def: def,
            cur: def,
        }
    }
}

fn on_clear_hash(_: &OptVal) {
    tt::clear();
}

fn on_hash_size(opt_val: &OptVal) {
    if let &OptVal::Spin { cur, .. } = opt_val {
        tt::resize(cur as usize);
    }
}

fn on_threads(opt_val: &OptVal) {
    if let &OptVal::Spin { cur, .. } = opt_val {
        threads::set(cur as usize);
    }
}

fn on_tb_path(opt_val: &OptVal) {
    if let &OptVal::StringOpt { ref cur, .. } = opt_val {
        tb::init(String::from(cur.as_str()));
    }
}

static mut OPTIONS: *mut Vec<Opt> = 0 as *mut Vec<Opt>;

pub fn init()
{
    let mut opts = Box::new(Vec::new());
    opts.push(Opt::new("Contempt", OptVal::spin(0, -100, 100), None));
    opts.push(Opt::new("Analysis Contempt", OptVal::check(false), None));
    opts.push(Opt::new("Threads", OptVal::spin(1, 1, 512), Some(on_threads)));
    opts.push(Opt::new("Hash", OptVal::spin(16, 1, 128 * 1024),
        Some(on_hash_size)));
    opts.push(Opt::new("Clear Hash", OptVal::Button, Some(on_clear_hash)));
    opts.push(Opt::new("Ponder", OptVal::check(false), None));
    opts.push(Opt::new("MultiPV", OptVal::spin(1, 1, 500), None));
    opts.push(Opt::new("Move Overhead", OptVal::spin(100, 0, 5000), None));
    opts.push(Opt::new("Minimum Thinking Time", OptVal::spin(20, 0, 5000),
        None));
    opts.push(Opt::new("Slow Mover", OptVal::spin(89, 10, 1000), None));
    opts.push(Opt::new("UCI_Analysis", OptVal::check(false), None));
    opts.push(Opt::new("UCI_Chess960", OptVal::check(false), None));
    opts.push(Opt::new("SyzygyPath", OptVal::string("<empty>"),
        Some(on_tb_path)));
    opts.push(Opt::new("SyzygyProbeDepth", OptVal::spin(1, 1, 100), None));
    opts.push(Opt::new("Syzygy50MoveRule", OptVal::check(true), None));
    opts.push(Opt::new("SyzygyProbeLimit", OptVal::spin(6, 0, 6), None));
    opts.push(Opt::new("SyzygyUseDTM", OptVal::check(true), None));
    unsafe {
        OPTIONS = Box::into_raw(opts);
    }
}

pub fn free()
{
    let _opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
}

pub fn print() {
    let opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
    for opt in opts.iter() {
        print!("\noption name {} type {}", opt.key, match opt.val {
            OptVal::StringOpt { def, .. } =>
                format!("string default {}", def),
            OptVal::Spin { def, min, max, .. } =>
                format!("spin default {} min {} max {}", def, min, max),
            OptVal::Check { def, .. } =>
                format!("check default {}", if def { true } else { false }),
            OptVal::Button => format!("button"),
        });
    }
    print!("\n");
    std::mem::forget(opts);
}

pub fn set(key: &str, val: &str) {
    let mut opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
    if let Some(opt) = opts.iter_mut().find(|ref o| o.key == key) {
        match opt.val {
            OptVal::StringOpt { ref mut cur, .. } => *cur = String::from(val),
            OptVal::Spin { ref mut cur, .. } =>
                *cur = val.parse::<i32>().unwrap(),
            OptVal::Check { ref mut cur, .. } => *cur = val == "true",
            OptVal::Button => {},
        }
        if let Some(on_change) = opt.on_change {
            on_change(&opt.val);
        }
    } else {
        println!("No such option: {}", key);
    }
    unsafe {
        OPTIONS = Box::into_raw(opts);
    }
}

pub fn get_i32(key: &str) -> i32 {
    let opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
    let val = {
        let opt = opts.iter().find(|ref o| o.key == key).unwrap();
        if let OptVal::Spin { cur, .. } = opt.val { cur } else { 0 }
    };
    std::mem::forget(opts);
    val
}

pub fn get_bool(key: &str) -> bool {
    let opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
    let val = {
        let opt = opts.iter().find(|ref o| o.key == key).unwrap();
        if let OptVal::Check { cur, .. } = opt.val { cur } else { false }
    };
    std::mem::forget(opts);
    val
}

pub fn get_string(key: &str) -> String {
    let opts: Box<Vec<Opt>> = unsafe { Box::from_raw(OPTIONS) };
    let val = {
        let opt = opts.iter().find(|ref o| o.key == key).unwrap();
        if let OptVal::StringOpt { ref cur, ..} = opt.val {
            String::from(cur.as_str())
        } else {
            String::new()
        }
    };
    std::mem::forget(opts);
    val
}
