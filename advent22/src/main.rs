use std::cmp::Ordering;
use std::collections::{HashSet,VecDeque};
use std::io::{self,BufRead};
use std::iter::FromIterator;

type Deck = VecDeque<u8>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Winner {
    Player1,
    Player2
}

fn read_input() -> (Deck, Deck) {
    let mut current = Deck::new();
    let mut other = Deck::new();

    let stdin = io::stdin();
    let stdin = stdin.lock();
    for line in stdin.lines() {
        let line = line.expect("No I/O errors");
        if line.starts_with("Player") {
            ()
        } else if line.is_empty() {
            std::mem::swap(&mut current, &mut other);
        } else {
            current.push_back(line.parse().expect("Integer input"))
        }
    }
    (other, current)
}

fn score(deck: &Deck) -> u64 {
    deck.iter().rev().copied().enumerate()
        .fold(0u64, |acc, (i, e)| acc + (((i as u64) + 1) * (e as u64)))
}

fn combat(mut deck1: Deck, mut deck2: Deck) -> u64 {
    while !(deck1.is_empty() || deck2.is_empty()) {
        let a = deck1.pop_front().unwrap();
        let b = deck2.pop_front().unwrap();
        match a.cmp(&b) {
            Ordering::Less => { deck2.push_back(b); deck2.push_back(a); }
            Ordering::Greater => { deck1.push_back(a); deck1.push_back(b); }
            Ordering::Equal => panic!("Tie in a game that can't have them"),
        }
    }
    if deck1.is_empty() { score(&deck2) } else { score(&deck1) }
}

fn recursive_combat(mut deck1: Deck, mut deck2: Deck) -> (Winner, u64) {
    let mut states = HashSet::<(Deck, Deck)>::new();
    while !(deck1.is_empty() || deck2.is_empty()) {
        // insert() returns false on duplicates
        if !states.insert((deck1.clone(), deck2.clone())) {
            return (Winner::Player1, score(&deck1));
        }
        let a = deck1.pop_front().unwrap();
        let b = deck2.pop_front().unwrap();
        if a as usize <= deck1.len() && b as usize <= deck2.len() {
            let recur_deck1 = Deck::from_iter(deck1.iter().copied().take(a as usize));
            let recur_deck2 = Deck::from_iter(deck2.iter().copied().take(b as usize));
            match recursive_combat(recur_deck1, recur_deck2) {
                (Winner::Player1, _) => { deck1.push_back(a); deck1.push_back(b); }
                (Winner::Player2, _) => { deck2.push_back(b); deck2.push_back(a); }
            }
        } else {
            match a.cmp(&b) {
                Ordering::Less => { deck2.push_back(b); deck2.push_back(a); }
                Ordering::Greater => { deck1.push_back(a); deck1.push_back(b); }
                Ordering::Equal => panic!("Tie in a game that can't have them"),
            }
        }
    }
    if deck1.is_empty() {
        (Winner::Player2, score(&deck2))
    } else {
        (Winner::Player1, score(&deck1))
    }
}

fn main() {
    let (deck1, deck2) = read_input();
    let soln_a = combat(deck1.clone(), deck2.clone());
    println!("Part a: {}", soln_a);
    let (winner, soln_b) = recursive_combat(deck1, deck2);
    println!("Part b: {} ({:?})", soln_b, winner);
}
