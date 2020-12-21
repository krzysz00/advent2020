use std::io::{self, BufRead};

use lazy_static::lazy_static;
use rustc_hash::FxHashSet;
use nalgebra::Vector4;

type V4 = Vector4<i32>;

lazy_static! {
    static ref OFFSETS: Vec<V4> = (-1..=1).flat_map(
        move |x| (-1..=1).flat_map(
            move |y| (-1..=1).flat_map(
                move |z| (-1..=1).filter_map(
                    move |w| if x != 0 || y != 0 || z != 0 || w != 0 {
                        Some(V4::new(x, y, z, w))
                    } else { None }))))
        .collect();
}

type PointSet = FxHashSet<V4>;

fn life4_update(alive: &PointSet) -> PointSet {
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
                ret.insert(V4::new(j, -i, 0, 0));
            }
        }
    }
    ret
}

fn part_b(input: PointSet) -> usize {
    let mut current = input;
    for _ in 0..6 {
        let new = life4_update(&current);
        current = new;
    }
    current.len()
}

fn main() {
    let input = read_input();
    let soln_b = part_b(input.clone());
    println!("Part b: {}", soln_b);
}
