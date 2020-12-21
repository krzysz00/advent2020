use std::io::{self, BufRead};

use lazy_static::lazy_static;
use rustc_hash::FxHashSet;
use nalgebra::Vector3;

type V3 = Vector3<i32>;

lazy_static! {
    static ref OFFSETS: Vec<V3> = (-1..=1).flat_map(
        move |x| (-1..=1).flat_map(
            move |y| (-1..=1).filter_map(
                move |z| if x != 0 || y != 0 || z != 0 { Some(V3::new(x, y, z)) } else { None })))
        .collect();
}

type PointSet = FxHashSet<V3>;

fn life3_update(alive: &PointSet) -> PointSet {
    let mut ret = PointSet::default();
    let mut maybe_alive = PointSet::default();

    for p in alive.iter() {
        let mut count = 0;
        for o in OFFSETS.iter() {
            let q = p + o;
            if alive.contains(&q) {
                count += 1;
            }
            else {
                maybe_alive.insert(q);
            }
        }
        if count == 2 || count == 3 {
            ret.insert(*p);
        }
    }
    for p in maybe_alive.drain() {
        let mut count = 0;
        for o in OFFSETS.iter() {
            let q = p + o;
            if alive.contains(&q) {
                count += 1;
                if count > 3 { break; }
            }
        }
        if count == 3 { ret.insert(p); }
    }
    ret
}

fn read_input() -> PointSet {
    let mut ret = PointSet::default();
    let stdin = io::stdin();
    let stdin = stdin.lock();
    for (i, l) in stdin.lines().enumerate() {
        let i = i as i32;
        let l = l.expect("No I/O errors");
        for (j, b) in l.bytes().enumerate() {
            let j = j as i32;
            if b == b'#' {
                ret.insert(V3::new(j, -i, 0));
            }
        }
    }
    ret
}

fn part_a(input: PointSet) -> usize {
    let mut current = input;
    for _ in 0..6 {
        let new = life3_update(&current);
        current = new;
    }
    current.len()
}

fn main() {
    let input = read_input();
    let soln_a = part_a(input.clone());
    println!("Part a: {}", soln_a);
}
