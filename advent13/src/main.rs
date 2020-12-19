use std::io::{self,BufRead};
use std::num::NonZeroU64;

type Err = Box<dyn std::error::Error + 'static>;

fn get_input() -> Result<(u64, Vec<Option<NonZeroU64>>), Err> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    let mut lines = stdin.lines();
    let line1 = lines.next().ok_or(Err::from("missing line 1"))?;
    let line1 = line1?;
    let timestamp = line1.parse::<u64>()?;
    let line2 = lines.next().ok_or(Err::from("missing line 2"))?;
    let line2 = line2?;
    let ids: Result<Vec<Option<NonZeroU64>>, Err> =
        line2.split(',').map(|s| {
            match s {
                "x" => Ok(None),
                s => s.parse::<NonZeroU64>().map(|x| Some(x)).map_err(|e| e.into()),
            }
        }).collect();
    let ids = ids?;
    Ok((timestamp, ids))
}

// (minimum time, timestamp)
fn part_a(timestamp: u64, ids: &[Option<NonZeroU64>]) -> (u64, u64) {
    ids.iter().copied().filter_map(|i| i.map(|x| {
        let x = x.get();
        let rem = timestamp % x;
        (if rem == 0 { 0 } else { x - rem }, x)
    })).min().expect("Nonempty part a")
}

// Inspiraiton: https://rosettacode.org/wiki/Chinese_remainder_theorem#Rust
fn egcd(a: i64, b: i64) -> (i64, i64, i64) {
    if a == 0 {
        (b, 0, 1)
    }
    else {
        let (g, x, y) = egcd(b % a, a);
        (g, y - ((b / a) * x), x)
    }
}

fn mod_inv(x: i64, n: i64) -> i64 {
    let (g, x, _) = egcd(x, n);
    if g == 1 {
        ((x % n) + n) % n
    }
    else {
        panic!("{} mod {} not coprime (g = {})", x, n, g);
    }
}

// Note: yes these need to be signed, egcd() relies on negative numbers exisitng
fn part_b(ids: &[Option<NonZeroU64>]) -> i64 {
    let prod = ids.iter().copied().filter_map(|x| x.map(|x| x.get() as i64)).product::<i64>();
    println!("Prod: {}", prod);
    let mut sum = 0i64;
    let len = ids.len() as i64;
    for (a, n) in (std::iter::once(0).chain(1..len))
        .zip(ids.iter().copied())
        .filter_map(|(a, n)| n.map(|x| (a, x.get() as i64)))
    {
        println!("{}, {}", a, n);
        let p = prod / n;
        sum += (a * mod_inv(p, n) * p) % prod;
    }
    sum % prod
}

fn main() -> Result<(), Err> {
    let (timestamp, ids) = get_input()?;
    let (min_time, bus_id) = part_a(timestamp, &ids);
    println!("Part a: {}", min_time * bus_id);
    let soln_b = part_b(&ids);
    println!("Part b: {}", soln_b);
    Ok(())
}
