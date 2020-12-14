use std::collections::HashSet;
use std::io::{BufRead};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Record {
    pub row: u32,
    pub col: u32,
}

impl Record {
    fn from_line(line: &[u8]) -> Self {
        let mut row = 0;
        let mut col = 0;
        for b in line {
            match b {
                b'F' => { row = row << 1; }
                b'B' => { row = (row << 1) | 1; }
                b'L' => { col = col << 1; }
                b'R' => { col = (col << 1) | 1; }
                b'\n' | b'\r' => (),
                c => panic!("Unexpected byte {}", c),
            }
        }
        Self {row, col}
    }

    pub fn ident(&self) -> u32 {
        self.col + 8 * self.row
    }
}

fn input() -> Vec<Record> {
    let mut buf = Vec::with_capacity(8 + 3 + 1);
    let mut ret = Vec::new();
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();
    loop {
        let len = stdin.read_until(b'\n', &mut buf).expect("No I/O errors");
        if len == 0 {
            return ret;
        }
        ret.push(Record::from_line(&buf));
        buf.clear();
    }
}

fn part_a(idents: &[u32]) -> u32 {
    idents.iter().copied().max().expect("Non-empty input")
}

// Pass in max from part a, save on recomputaiton
fn part_b(idents: &[u32], max: u32) -> u32 {
    let min = idents.iter().copied().min().expect("Non-empty input");
    let mut seats = HashSet::with_capacity((max - min) as usize);
    seats.extend(min..max);
    for ident in idents {
        seats.remove(ident);
    }
    seats.remove(&min);
    seats.remove(&max);
    if seats.len() != 1 {
        panic!("Non-unique seats: {:?}", seats)
    }
    seats.iter().copied().nth(0).expect("A solution to exist")
}

fn main() {
    let data = input();
    let idents = data.iter().map(|x| x.ident()).collect::<Vec<u32>>();
    let soln_a = part_a(&idents);
    println!("Part a: {}", soln_a);
    let soln_b = part_b(&idents, soln_a);
    println!("Part b: {}", soln_b);
}
