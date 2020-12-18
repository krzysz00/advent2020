use std::io::{self, BufRead};
use ndarray::{Array2,ArrayView2, Ix};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Seat {
    Floor,
    Empty,
    Occupied,
}

fn occupied_a(state: ArrayView2<Seat>, (i, j): (Ix, Ix)) -> usize {
    let mut count = 0;
    for &ii in [i.wrapping_sub(1), i, i + 1].iter() {
        for &jj in [j.wrapping_sub(1), j, j + 1].iter() {
            if  state.get((ii, jj)).copied().unwrap_or(Seat::Floor) == Seat::Occupied {
                count += 1;
            }
        }
    }
    count
}

fn occupied_b(state: ArrayView2<Seat>, (i, j): (Ix, Ix)) -> usize {
    let mut count = if state[(i, j)] == Seat::Occupied { 1 } else { 0 };
    let i = i as isize;
    let j = j as isize;

    for &delta_i in [-1, 0, 1].iter() {
        for &delta_j in [-1, 0, 1].iter() {
            if delta_i == 0 && delta_j == 0 { continue; }
            let mut idx_i = i.wrapping_add(delta_i);
            let mut idx_j = j.wrapping_add(delta_j);
            while match state.get((idx_i as usize, idx_j as usize)).copied() {
                Some(Seat::Empty) => false,
                Some(Seat::Occupied) => { count += 1; false },
                Some(Seat::Floor) => true,
                None => false
            } {
                idx_i = idx_i.wrapping_add(delta_i);
                idx_j = idx_j.wrapping_add(delta_j);
            }
        }
    }
    count
}

fn input() -> Array2<Seat> {
    let mut m = 0;
    let mut n = 0;
    let mut ret = Vec::new();

    let stdin = io::stdin();
    let stdin = stdin.lock();
    for line in stdin.lines() {
        let line = line.expect("No I/O errors");
        let n_curr = line.len();
        if n_curr == 0 {
            continue;
        }
        if n == 0 {
            n = n_curr;
        }
        if n_curr != n {
            panic!("Uneven input: {} is not {}", n_curr, n)
        }
        m += 1;
        ret.extend(line.bytes().map(|b| {
            match b {
                b'L' => Seat::Empty,
                b'#' => Seat::Occupied,
                b'.' => Seat::Floor,
                _ => panic!("Unexpected byte: {}", b),
            }
        }))
    }
    Array2::from_shape_vec((m, n), ret).expect("Validly-shaped array")
}


fn update<F>(state: ArrayView2<Seat>, count: F, tol: usize) -> Array2<Seat>
where F: Fn(ArrayView2<Seat>, (usize, usize)) -> usize {
    Array2::from_shape_fn(state.raw_dim(),
                          |idx| {
                              match state[idx] {
                                  Seat::Floor => Seat::Floor,
                                  Seat::Empty =>
                                      if count(state, idx) == 0 { Seat::Occupied } else { Seat::Empty },
                                  Seat::Occupied => // the conv overcounts by 1
                                      if count(state, idx) > tol { Seat::Empty } else { Seat::Occupied },
                              }
                          })
}

fn solve<F>(input: Array2<Seat>, count: F, tol: usize) -> usize
where F: Fn(ArrayView2<Seat>, (usize, usize)) -> usize  {
    let mut current = input;
    let mut next = update(current.view(), &count, tol);
    while current != next {
        current = next;
        next = update(current.view(), &count, tol);
    }
    current.iter().copied().filter(|&v| v == Seat::Occupied).count()
}


fn main() {
    let input = input();
    let part_a = solve(input.clone(), occupied_a, 4);
    println!("Part a: {}", part_a);
    let part_b = solve(input.clone(), occupied_b, 5);
    println!("Part b: {}", part_b);
}
