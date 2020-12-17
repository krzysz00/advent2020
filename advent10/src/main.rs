use std::cmp::Reverse;
use std::io::{self, BufRead};
use std::collections::BinaryHeap;

type Err = Box<dyn std::error::Error + 'static>;

fn part_a(input: &[u32]) -> u32 {
    let mut current = 0;
    let mut deltas = [0, 0, 0];
    let mut heap = input.iter().copied().map(Reverse).collect::<BinaryHeap<_>>();
    while let Some(Reverse(next)) = heap.pop() {
        let delta = next - current;
        deltas[delta as usize - 1] += 1;
        current = next;
    }
    deltas[2] += 1;
    deltas[0] * deltas[2]
}

fn part_b(input: &[u32]) -> Result<u64, Err> {
    let mut data = input.iter().copied().map(|x| x as usize).collect::<Vec<_>>();
    data.sort_unstable();
    let max = data.last().copied().ok_or(Err::from("empty input"));
    let max = max?;

    let mut table = vec![0u64; max + 1];
    table[0] = 1;

    for adapter in data {
        table[adapter] = table.get(adapter.wrapping_sub(1)).copied().unwrap_or(0)
            + table.get(adapter.wrapping_sub(2)).copied().unwrap_or(0)
            + table.get(adapter.wrapping_sub(3)).copied().unwrap_or(0);
    }
    Ok(table[max])
}

fn input() -> Result<Vec<u32>, Err> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    stdin.lines().map(|l| {
        l.map_err(Err::from)
            .and_then(|s| s.parse::<u32>().map_err(Err::from))
    }).collect()
}

fn main() -> Result<(), Err> {
    let input = input()?;
    let soln_a = part_a(&input);
    println!("Part a: {}", soln_a);
    let soln_b = part_b(&input)?;
    println!("Part b: {}", soln_b);
    Ok(())
}
