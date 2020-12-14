use std::io;
use std::io::BufRead;

type Record = u32;
fn parse() -> Vec<Record> {
    let stdin = io::stdin();
    let stdin = stdin.lock();

    let mut ret = Vec::new();
    let mut record = 0;

    for line in stdin.lines() {
        let line = line.expect("No I/O errors");
        for b in line.bytes() {
            if b < b'a' || b > b'z' {
                panic!{"Invalid input byte: {}", b};
            }
            let question = b - b'a';
            record |= 1 << question;
        }
        if line.len() == 0 {
            ret.push(record);
            record = 0;
        }
    }
    if record != 0 {
        ret.push(record);
    }
    ret
}

fn part_a(input: &[Record]) -> u32 {
    input.iter().map(|x| x.count_ones()).sum()
}

fn main() {
    let input = parse();
    let soln_a = part_a(&input);
    println!("Part a: {}", soln_a);
}
