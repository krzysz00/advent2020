use std::io;
use std::io::BufRead;

type Record = u32;
fn parse() -> Vec<Record> {
    let stdin = io::stdin();
    let stdin = stdin.lock();

    let mut ret = Vec::new();
    let mut record = None;

    for line in stdin.lines() {
        let line = line.expect("No I/O errors");
        if line.len() == 0 {
            if let Some(r) = record {
                ret.push(r);
            }
            record = None;
        }
        else {
            let mut this_person = 0;
            for b in line.bytes() {
                if b < b'a' || b > b'z' {
                    panic!{"Invalid input byte: {}", b};
                }
                let question = b - b'a';
                this_person |= 1 << question;
            }
            *record.get_or_insert(this_person) &= this_person;
        }
    }
    if let Some(r) = record {
        ret.push(r);
    }
    ret
}

fn part_b(input: &[Record]) -> u32 {
    input.iter().map(|x| x.count_ones()).sum()
}

fn main() {
    let input = parse();
    let soln_b = part_b(&input);
    println!("Part b: {}", soln_b);
}
