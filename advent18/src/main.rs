use std::io::{self, BufRead};

use lazy_static::lazy_static;
use regex::Regex;

type Error = Box<dyn std::error::Error + 'static>;
type Result<T> = std::result::Result<T, Error>;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Token {
    Plus,
    Times,
    LParen,
    RParen,
    Number(i64),
}

fn lex(input: &str) -> Result<Vec<Token>> {
    lazy_static! {
        static ref TOKEN: Regex = Regex::new(r"\d+|\+|\*|\(|\)").unwrap();
    }
    TOKEN.find_iter(input).map(|tok| {
        match tok.as_str() {
            "+" => Ok(Token::Plus),
            "*" => Ok(Token::Times),
            "(" => Ok(Token::LParen),
            ")" => Ok(Token::RParen),
            s => s.parse::<i64>().map_err(Error::from).map(Token::Number)
        }
    }).collect::<Result<Vec<_>>>()
}

fn get_input() -> Result<Vec<Vec<Token>>> {
    let stdin = io::stdin();
    let stdin = stdin.lock();
    stdin.lines().map(|l| l.map_err(Error::from)
                      .and_then(|l| lex(&l))).collect::<Result<Vec<_>>>()
}

fn compute(toks: &[Token], pos: usize) -> Result<(usize, i64)> {
    if pos >= toks.len() { return Err(Error::from("Computation out of bounds" )) }

    let (mut pos, mut accum) = match toks[pos] {
        Token::Number(v) => (pos + 1, v),
        Token::LParen => compute(toks, pos + 1)?,
        _ => return Err(Error::from(format!("Expected number or (, got {:?} at {}", toks[pos], pos)))
    };
    while pos < toks.len() && toks[pos] != Token::RParen {
        let op = toks[pos];
        pos += 1;
        let (new_pos, right) = match toks[pos] {
            Token::Number(v) => (pos + 1, v),
            Token::LParen => compute(toks, pos + 1)?,
            _ => return Err(Error::from(format!("Expected number or (, got {:?} at {}", toks[pos], pos))),
        };
        pos = new_pos;
        match op {
            Token::Plus => { accum = accum + right; }
            Token::Times => { accum = accum * right; }
            _ => return Err(Error::from("Only supported operations are + and *")),
        }
    }
    Ok((pos + 1, accum))
}

fn eval_line(input: &[Token]) -> Result<i64> {
    let (loc, ret) = compute(input, 0)?;
    if loc < input.len() {
        Err(Error::from(format!("Underconsumed input: {} of {}", loc, input.len())))
    } else {
        Ok(ret)
    }
}


fn part_a(input: &[Vec<Token>]) -> Result<i64> {
    input.iter().map(|x| eval_line(x)).sum::<Result<i64>>()
}

// E := E2 | E2 '*' E
// E2 := E3 | E3 '+' E2
// E3 := Num | '( E ')'
#[derive(Clone, Debug)]
enum Expr {
    Number(i64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}


fn parse_e(toks: &[Token], pos: usize) -> Result<(usize, Expr)> {
    let (pos, left) = parse_e2(toks, pos)?;
    if toks.get(pos).copied() == Some(Token::Times) {
        let (pos, right) = parse_e(toks, pos + 1)?;
        Ok((pos, Expr::Mul(Box::new(left), Box::new(right))))
    } else {
        Ok((pos, left))
    }
}

fn parse_e2(toks: &[Token], pos: usize) -> Result<(usize, Expr)> {
    let (pos, left) = parse_e3(toks, pos)?;
    if toks.get(pos).copied() == Some(Token::Plus) {
        let (pos, right) = parse_e2(toks, pos + 1)?;
        Ok((pos, Expr::Add(Box::new(left), Box::new(right))))
    } else {
        Ok((pos, left))
    }
}

fn parse_e3(toks: &[Token], pos: usize) -> Result<(usize, Expr)> {
    match toks.get(pos).copied().
        ok_or_else(|| Error::from("expected right operand, got EOL"))?
    {
        Token::Number(v) => Ok((pos + 1, Expr::Number(v))),
        Token::LParen => {
            let (pos2, e) = parse_e(toks, pos + 1)?;
            if toks.get(pos2).copied() != Some(Token::RParen) {
                Err(Error::from(format!("Uncloned group - {} to {}", pos, pos2)))
            } else { Ok((pos2 + 1, e)) }
        },
        t => Err(Error::from(format!("Unexpected token {:?} at {}", t, pos))),
    }
}

fn eval_expr(e: &Expr) -> i64 {
    match e {
        Expr::Number(v) => *v,
        Expr::Add(e1, e2) => eval_expr(e1) + eval_expr(e2),
        Expr::Mul(e1, e2) => eval_expr(e1) * eval_expr(e2),
    }
}

fn part_b(input: &[Vec<Token>]) -> Result<i64> {
    input.iter().map(|toks| {
        parse_e(toks, 0).and_then(|(len, e)| {
            if len < toks.len() {
                Err(Error::from(format!("Underused line: used {} of {} tokens", len, toks.len())))
            } else {
                Ok(eval_expr(&e))
            }
        })
    }).sum::<Result<i64>>()
}

fn main() -> Result<()> {
    let input = get_input()?;
    let soln_a = part_a(&input)?;
    println!("Part a: {}", soln_a);
    let soln_b = part_b(&input)?;
    println!("Part b: {}", soln_b);
    Ok(())
}
