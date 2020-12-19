use std::collections::HashMap;
use std::io::{self, BufRead};
use std::str::FromStr;

use lazy_static::lazy_static;
use regex::Regex;

type Error = Box<dyn std::error::Error + 'static>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stmt {
    Set { loc: u64, val: u64 },
    Mask(String),
}

impl FromStr for Stmt {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        lazy_static! {
            static ref RE_MASK: Regex = Regex::new(r"^mask = ([01X]{36})$").unwrap();
            static ref RE_MEM: Regex = Regex::new(r"^mem\[(\d+)\] = (\d+)$").unwrap();
        }

        if let Some(matches) = RE_MASK.captures(s) {
            Ok(Stmt::Mask(matches[1].to_owned()))
        } else if let Some(matches) = RE_MEM.captures(s) {
            let loc = matches[1].parse::<u64>()?;
            let val = matches[2].parse::<u64>()?;
            Ok(Stmt::Set { loc, val })
        } else {
            Err(Error::from("not a valid statement"))
        }
    }
}

fn get_input() -> Result<Vec<Stmt>> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    stdin.lines().map(|l| l.map_err(|e| Error::from(e))
                      .and_then(|l| l.parse::<Stmt>()))
        .collect()
}

trait Interpreter {
    fn new() -> Self;
    fn set_mask(&mut self, s: &str);
    fn write(&mut self, loc: u64, val: u64);
    fn mem_sum(&self) -> u64;
}

#[derive(Clone, Debug)]
struct StateA {
    mem: HashMap<u64, u64>,
    and_mask: u64,
    or_mask: u64,
}

const ONES: u64 = (1 << 36) - 1;

impl Interpreter for StateA {
    fn new() -> Self {
        Self { mem: HashMap::new(), and_mask: ONES, or_mask: 0 }
    }

    fn set_mask(&mut self, s: &str) {
        let mut new_and = ONES;
        let mut new_or = 0;
        for (i, b) in s.bytes().rev().enumerate() {
            let i = i as u64;
            match b {
                b'0' => { new_and &= !(1 << i); }
                b'1' => { new_or |= 1 << i; },
                b'X' => (),
                _ => unreachable!(),
            }
        }
        self.and_mask = new_and;
        self.or_mask = new_or;
    }

    fn write(&mut self, loc: u64, raw_val: u64) {
        self.mem.insert(loc, (raw_val | self.or_mask) & self.and_mask);
    }

    fn mem_sum(&self) -> u64 {
        self.mem.values().copied().sum()
    }
}

#[derive(Clone, Debug)]
struct StateB {
    mem: HashMap<u64, u64>,
    masks: Vec<(u64, u64)>,
}

impl Interpreter for StateB {
    fn new() -> Self {
        Self { mem: HashMap::new(), masks: vec![(0, ONES)] }
    }

    fn set_mask(&mut self, s: &str) {
        let mut base_or = 0;
        let mut floating = Vec::new();
        for (i, b) in s.bytes().rev().enumerate() {
            let i = i as u64;
            match b {
                b'1' => { base_or |= 1 << i; },
                b'X' => { floating.push(i); }
                b'0' => (),
                _ => unreachable!(),
            }
        }
        let mut masks = vec![(base_or, ONES)];
        for i in floating {
            let mut new_masks = Vec::with_capacity(masks.len() * 2);
            for (or, and) in masks {
                new_masks.push((or | (1 << i), and));
                new_masks.push((or, and & !(1 << i)));
            }
            masks = new_masks;
        }
        self.masks = masks;
    }

    fn write(&mut self, loc: u64, val: u64) {
        for &(or, and) in &self.masks {
            self.mem.insert((loc | or) & and, val);
        }
    }

    fn mem_sum(&self) -> u64 {
        self.mem.values().copied().sum()
    }
}

fn run<T: Interpreter>(prog: &[Stmt]) -> u64 {
    let mut state = T::new();
    for stmt in prog {
        match stmt {
            Stmt::Mask(s) => state.set_mask(s),
            Stmt::Set { loc, val } => state.write(*loc, *val)
        }
    }
    state.mem_sum()
}

fn main() -> Result<()> {
    let input = get_input()?;
    let soln_a = run::<StateA>(&input);
    println!("Part a: {}", soln_a);
    let soln_b = run::<StateB>(&input);
    println!("Part b: {}", soln_b);
    Ok(())
}
