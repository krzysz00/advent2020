use std::io::{self,BufRead};

use lazy_static::lazy_static;
use regex::Regex;

fn extending_set<T>(vec: &mut Vec<Option<T>>, idx: usize, val: T) {
    for _ in vec.len()..=idx {
        vec.push(None);
    }
    vec[idx] = Some(val)
}

#[derive(Clone, Debug)]
enum Rule {
    Literal(String),
    Seq(Vec<usize>),
    Alt(Vec<usize>, Vec<usize>),
}

fn parse_int(s: &str) -> usize {
    s.parse::<usize>().expect("Integers to be integers")
}

fn parse_ints(s: &str) -> Vec<usize> {
    s.split_whitespace().map(parse_int).collect()
}

fn parse_rule(s: &str) -> (usize, Rule) {
    lazy_static! {
        //static ref RE: Regex = Regex::new("for syntax highlight").unwrap();
        static ref RE: Regex = Regex::new(r#"([0-9]+): (?:"([^"]+)"|([0-9 ]+)$|([0-9 ]+) \| ([0-9 ]+))"#).unwrap();
    }
    let captures = RE.captures(s).expect("input to match rule format");
    let idx = parse_int(captures.get(1).unwrap().as_str());
    let rule =
        if let Some(m) = captures.get(2) {
            Rule::Literal(m.as_str().to_owned())
        } else if let Some(digits) = captures.get(3) {
            Rule::Seq(parse_ints(digits.as_str()))
        } else if let Some(left) = captures.get(4) {
            Rule::Alt(parse_ints(left.as_str()), parse_ints(captures.get(5).unwrap().as_str()))
        } else {
            unreachable!{};
        };
    (idx, rule)
}

fn get_input() -> (Vec<Option<Rule>>, Vec<String>) {
    let stdin = io::stdin();
    let rules = {
        let stdin = stdin.lock();
        let mut map: Vec<Option<Rule>> = vec![];
        stdin.lines().take_while(|l| l.as_ref().map(|s| s != "").unwrap_or(true))
            .for_each(|l| {
                let (i, r) = parse_rule(&l.expect("No I/O errors"));
                extending_set(&mut map, i, r);
            });
        map
    };
    let messages = {
        let stdin = stdin.lock();
        stdin.lines().map(|l| l.expect("No I/O errors")).collect::<Vec<_>>()
    };
    (rules, messages)
}

fn dp_regex_seq(input: &[Option<Rule>], map: &mut Vec<Option<String>>,
                idxs: &[usize]) -> String {
    let mut ret = String::new();
    idxs.iter().copied().for_each(|i| {
        if i >= map.len() || map[i].is_none() {
            dp_regex(input, map, i);
        }
        ret.push_str(map[i].as_ref().unwrap());
    });
    ret
}

fn dp_regex(input: &[Option<Rule>], map: &mut Vec<Option<String>>, idx: usize) {
    match input[idx].as_ref().expect("No gaps in rules") {
        Rule::Literal(s) => extending_set(map, idx, s.clone()),
        Rule::Seq(sub) => {
            let ret = dp_regex_seq(input, map, sub);
            extending_set(map, idx, ret);
        },
        Rule::Alt(left, right) => {
            let left = dp_regex_seq(input, map, left);
            let right = dp_regex_seq(input, map, right);
            extending_set(map, idx, format!("(?:{}|{})", left, right));
        }
    }
}

fn build_regex(rules: &[Option<Rule>]) -> Regex {
    let mut map: Vec<Option<String>> = vec![];
    dp_regex(rules, &mut map, 0);
    let re: &str = map[0].as_ref().expect("Element 0 to be filled");
    let re = format!("^(?:{})$", re);
    Regex::new(&re).expect("Valid regex to be made")
}

fn part_a(rules: &[Option<Rule>], messages: &[String]) -> usize {
    let re = build_regex(rules);
    messages.iter().filter(|s| re.is_match(s)).count()
}

fn main() {
    let (rules, messages) = get_input();
    let soln_a = part_a(&rules, &messages);
    println!("Part a: {}", soln_a);
}
