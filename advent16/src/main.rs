use std::io::{self, BufRead};
use std::iter::FromIterator;
use std::str::FromStr;

use lazy_static::lazy_static;
use regex::Regex;
use tinyset::SetUsize;

type Error = Box<dyn std::error::Error + 'static>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug)]
struct Field {
    name: String,
    min1: u64,
    max1: u64,
    min2: u64,
    max2: u64
}

impl Field {
    pub fn new(name: String, min1: u64, max1: u64, min2: u64, max2: u64) -> Self {
        Self { name, min1, max1, min2, max2 }
    }

    pub fn valid(&self, value: u64) -> bool {
        (value >= self.min1 && value <= self.max1) || (value >= self.min2 && value <= self.max2)
    }

    pub fn departure(&self) -> bool {
        self.name.starts_with("departure ")
    }
}

impl FromStr for Field {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^([a-z ]+): (\d+)-(\d+) or (\d+)-(\d+)").unwrap();
        }
        let matches = RE.captures(s).ok_or(Error::from("unparsable field"))?;
        let name = matches[1].to_owned();
        let min1 = matches[2].parse::<u64>()?;
        let max1 = matches[3].parse::<u64>()?;
        let min2 = matches[4].parse::<u64>()?;
        let max2 = matches[5].parse::<u64>()?;
        Ok(Self::new(name, min1, max1, min2, max2))
    }
}

type Ticket = Vec<u64>;

const ME_HEADER: &str = "your ticket:";
const THEIR_HEADER: &str = "nearby tickets:";

fn parse_ticket(s: &str) -> Result<Ticket> {
    s.split(',').map(|x| x.parse::<u64>().map_err(Error::from)).collect()
}

fn get_input() -> Result<(Vec<Field>, Ticket, Vec<Ticket>)> {
    let stdin = io::stdin();
    let fields = {
        let stdin = stdin.lock();
        stdin.lines().take_while(|l| l.as_ref().map(|s| s != "").unwrap_or(true))
            .map(|l| l.map_err(Error::from).and_then(|s| s.parse::<Field>()))
            .collect::<Result<Vec<_>>>()
    };
    let fields = fields?;
    let my_ticket = {
        let mut line = String::with_capacity(THEIR_HEADER.len());
        let mut stdin = stdin.lock();
        stdin.read_line(&mut line)?;
        if line.trim() != ME_HEADER {
            return Err(Error::from("malformed ticket headers"));
        }
        line.clear();
        stdin.read_line(&mut line)?;
        let ticket = parse_ticket(line.trim())?;
        line.clear();
        stdin.read_line(&mut line)?;
        if line != "\n" {
            return Err(Error::from("missing blank line"));
        }
        line.clear();
        stdin.read_line(&mut line)?;
        if line.trim() != THEIR_HEADER {
            return Err(Error::from("malformed related tickets header"));
        }
        ticket
    };
    let stdin = stdin.lock();
    let related = stdin.lines().map(|l| l.map_err(Error::from)
                                    .and_then(|l| parse_ticket(&l)))
        .collect::<Result<Vec<Ticket>>>()?;
    Ok((fields, my_ticket, related))
}

fn part_a(fields: &[Field], tickets: &[Ticket]) -> u64 {
    tickets.iter().flat_map(|t| t.iter().copied()
                            .filter(|&v| fields.iter().all(|f| !f.valid(v))))
        .sum()
}

fn part_b(fields: &[Field], my_ticket: &Ticket, tickets: &[Ticket]) -> u64 {
    let mut valid_tickets: Vec<&[u64]> =
        tickets.iter().filter_map(|t| {
            if t.iter().copied().all(|v| fields.iter().any(|f| f.valid(v))) {
                Some(t.as_slice())
            } else { None }
        }).collect();
    valid_tickets.push(my_ticket);

    let n_fields = fields.len();
    let mut sets: Vec<_> = (0..n_fields)
        .map(|_| SetUsize::from_iter(0..n_fields)).collect();
    for t in valid_tickets {
        for (i, v) in t.iter().copied().enumerate() {
            for (j, f) in fields.iter().enumerate() {
                if !f.valid(v) {
                    sets[i].remove(j);
                }
            }
        }
    }

    let mut field_to_ticket_idx: Vec<Option<usize>> = vec![None; n_fields];
    let mut fields_set = 0;
    let mut to_remove = vec![];
    while fields_set < n_fields {
        for (i, s) in sets.iter().enumerate() {
            if s.len() == 1 {
                let field = s.iter().next().unwrap();
                field_to_ticket_idx[field] = Some(i);
                fields_set += 1;
                to_remove.push(field);
            }
        }
        for v in to_remove.drain(..) {
            for s in &mut sets {
                s.remove(v);
            }
        }
    }

    let field_to_ticket_idx = field_to_ticket_idx.into_iter()
        .collect::<Option<Vec<_>>>().expect("All fields set");
    fields.iter().enumerate().filter_map(|(i, f)| {
        if f.departure() { Some(my_ticket[field_to_ticket_idx[i]]) } else { None }
    }).product()
}

fn main() -> Result<()> {
    let (fields, my_ticket, related_tickets) = get_input()?;
    let soln_a = part_a(&fields, &related_tickets);
    println!("Part a: {}", soln_a);
    let soln_b = part_b(&fields, &my_ticket, &related_tickets);
    println!("Part b: {}", soln_b);
    Ok(())
}
