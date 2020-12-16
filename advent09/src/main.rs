use std::collections::{VecDeque,HashSet};
use std::io::{self, BufRead};

const PREAMBLE_LENGTH: usize = 25;

#[derive(Debug)]
struct State {
    numbers: VecDeque<u64>,
    sets: VecDeque<HashSet<u64>>,
}

impl State {
    pub fn new(preamble: Vec<u64>) -> Self {
        let numbers = VecDeque::from(preamble);
        let sets: VecDeque<HashSet<u64>> =
            numbers.iter().copied().enumerate()
            .map(|(idx_i, i)|
                 numbers.iter().copied().enumerate()
                 .filter(|&(idx_j, _)| idx_i != idx_j)
                 .map(|(_, j)| i + j).collect())
            .collect();
        Self { numbers, sets }
    }

    pub fn valid(&self, n: u64) -> bool {
        self.sets.iter().any(|h| h.contains(&n))
    }

    pub fn push(&mut self, n: u64) {
        self.numbers.pop_front();
        self.sets.pop_front();
        let new_set: HashSet<u64> = self.numbers.iter().copied()
            .map(move |i| i + n).collect();
        self.numbers.push_back(n);
        self.sets.push_back(new_set);
    }
}

fn input() -> Vec<u64> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    stdin.lines()
        .map(|l| l.expect("No I/O errors").parse::<u64>().expect("Integer input"))
        .collect()
}

fn part_a(input: &[u64]) -> Option<u64> {
    let (preamble, digits) = input.split_at(PREAMBLE_LENGTH);
    let mut state = State::new(preamble.to_owned());
    for i in digits.iter().copied() {
        if !state.valid(i) {
            return Some(i);
        }
        state.push(i);
    }
    None
}

fn part_b(input: &[u64], soln_a: u64) -> u64 {
    let len = input.len();
    for i in 0..len {
        let mut sum = 0;
        for j in i..len {
            sum += input[j];
            if sum == soln_a {
                let min = input[i..j].iter().copied().min().expect("Non-empty range");
                let max = input[i..j].iter().copied().max().expect("Non-empty range");
                return min + max;
            }
            if sum > soln_a {
                break;
            }
        }
    }
    panic!("No solution to part b")
}

fn main() {
    let input = input();
    let soln_a = part_a(&input).expect("Part a to be solvable");
    println!("Part a: {}", soln_a);
    let soln_b = part_b(&input, soln_a);
    println!("Part b: {}", soln_b);
}
