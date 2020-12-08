use std::str::FromStr;
use std::io::{BufRead};

use lazy_static::lazy_static;
use regex::Regex;

#[derive(Clone, Debug)]
pub struct Entry {
    first: usize,
    second: usize,
    character: char,
    value: String,
}

impl FromStr for Entry {
    type Err = Box<dyn std::error::Error + 'static>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"(\d+)-(\d+) (.): (\w+)").unwrap();
        }
        let parsed = RE.captures(s).ok_or("no match")?;
        let first = parsed[1].parse::<usize>()?;
        let second = parsed[2].parse::<usize>()?;
        let character = parsed[3].chars().nth(0).unwrap();
        let value = parsed[4].to_string();
        Ok(Entry { first, second, character, value })
    }
}

impl Entry {
    pub fn valid_a(&self) -> bool {
        let count = self.value.chars().filter(|c| *c == self.character).count();
        count >= self.first && count <= self.second
    }

    pub fn valid_b(&self) -> bool {
        let a_set = self.value.chars().nth(self.first - 1).map(|c| c == self.character);
        // Re-iterates, we can deal with it later
        let b_set = self.value.chars().nth(self.second - 1).map(|c| c == self.character);
        match (a_set, b_set) {
            (Some(p), Some(q)) => p ^ q,
            _ => false
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error + 'static>> {
    let stdin = std::io::stdin();
    let stdin = stdin.lock();
    let data: Result<Vec<Entry>, _> = stdin.lines().map(|l| l.unwrap().parse::<Entry>()).collect();
    let data = data?;

    let part_a = data.iter().filter(|x| x.valid_a()).count();
    let part_b = data.iter().filter(|x| x.valid_b()).count();
    println!("Part a: {}\nPart b: {}", part_a, part_b);
    Ok(())
}
