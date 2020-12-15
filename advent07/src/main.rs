use std::collections::{HashMap, HashSet};
use std::io::BufRead;
use std::rc::Rc;

use lazy_static::lazy_static;
use regex::Regex;

#[derive(Clone, Debug, Default)]
struct Edges {
    pub parents: Vec<Rc<String>>,
    pub children: Vec<(u32, Rc<String>)>
}

impl Edges {
    pub fn new() -> Self {
        Self { parents: vec![], children: vec![] }
    }
}

#[derive(Clone, Debug)]
struct Graph {
    data: HashMap<Rc<String>, Edges>
}

impl Graph {
    pub fn new() -> Self { Self { data: HashMap::new() } }

    pub fn add_node(&mut self, node: String, out_edges: Vec<(u32, String)>) {
        let node = Rc::new(node);
        let mut children = Vec::new();
        for (weight, u) in out_edges {
            let u = Rc::new(u);
            self.data.entry(u.clone()).or_insert_with(Edges::new)
                .parents.push(node.clone());
            children.push((weight, u));
        }
        self.data.entry(node.clone()).or_insert_with(Edges::new)
            .children.append(&mut children);
    }

    fn dfs_walk_up(&self, node: &Rc<String>, visited: &mut HashSet<Rc<String>>) {
        if !visited.insert(node.clone()) { // Already in visited set
            return;
        }
        self.data.get(node).map(
            |edges| edges.parents.iter()
            .for_each(|v| { self.dfs_walk_up(v, visited); }));
    }

    fn dfs_weights_below(&self, node: &Rc<String>, results: &mut HashMap<Rc<String>, u32>) -> u32 {
        if let Some(c) = results.get(node).copied() {
            return c;
        }
        let ret = self.data.get(node).map(|edges| {
            edges.children.iter().map(|(w, ref v)| {
                w * (1 + self.dfs_weights_below(v, results))
            }).sum()
        }).unwrap_or(0);
        results.insert(node.clone(), ret);
        ret
    }

    pub fn ancestors_of(&self, key: &Rc<String>) -> HashSet<Rc<String>> {
        let mut ret = HashSet::new();
        self.dfs_walk_up(key, &mut ret);
        ret
    }

    pub fn bags_below(&self, key: &Rc<String>) -> (u32, HashMap<Rc<String>, u32>) {
        let mut cache = HashMap::with_capacity(self.data.len());
        let sum = self.dfs_weights_below(key, &mut cache);
        (sum, cache)
    }
}

fn parse_line(graph: &mut Graph, line: &str) {
    lazy_static! {
        static ref RE_ALL: Regex = Regex::new(r"(.+) bags contain (.*)\.$").unwrap();
        static ref RE_SPLIT: Regex = Regex::new(r" bags?,? ?").unwrap();
        static ref RE_EDGE: Regex = Regex::new(r"^(\d+) (.+)\s*$").unwrap();
    }
    let unpack = RE_ALL.captures(line).expect("Input to match");
    let key = unpack[1].to_owned();
    if &unpack[2] == "no other bags" {
        graph.add_node(key, vec![]);
    }
    else {
        let edges = RE_SPLIT.split(&unpack[2])
            .filter(|m| !m.is_empty())
            .map(|m| {
                let edge_parts = RE_EDGE.captures(m).expect("bag format in edge");
                let weight = edge_parts[1].parse::<u32>().expect("Integers to be integers");
                let key = edge_parts[2].to_owned();
                (weight, key)
            }).collect();
        graph.add_node(key, edges);
    }
}

fn read() -> Graph {
    let stdin = std::io::stdin();
    let stdin = stdin.lock();
    let mut ret = Graph::new();
    stdin.lines().for_each(|l| {
        let l = l.expect("No I/O errors");
        parse_line(&mut ret, &l);
    });
    ret
}

fn main() {
    let input = read();
    let key = Rc::new("shiny gold".to_owned());
    let part_a = input.ancestors_of(&key);
    //println!("Part a solution: {:?}", part_a);
    println!("Part a: {}", part_a.len() - 1); // Don't count ourselves
    let (part_b, _part_b_detail) = input.bags_below(&key);
    println!("Part b: {}", part_b);
}
