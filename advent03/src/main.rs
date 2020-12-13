use std::io::Read;

struct Input {
    data: Vec<bool>,
    m: usize,
    n: usize,
}

impl Input {
    pub fn get(&self, i: usize, j: usize) -> Option<bool> {
        self.data.get((j % self.n) + i * self.n).copied()
    }

    pub fn parse(input: String) -> Self {
        let mut m = 0;
        let mut n = 0;
        let mut n_curr = 0;
        let mut ret = Vec::with_capacity(input.len());

        for b in input.bytes() {
            match b {
                b'\n' => {
                    if n == 0 {
                        n = n_curr;
                    }
                    else if n != n_curr {
                        panic!("Uneven line lengths: {} != original {}", n_curr, n);
                    }
                    m += 1;
                    n_curr = 0;
                },
                b'#' | b'.' => {
                    ret.push(b == b'#');
                    n_curr += 1;
                },
                _ => {}
            }
        }

        if n_curr != 0 {
            // No trailing newline
            m += 1;
        }

        Self { data: ret, m, n }
    }

    fn walk(&self, di: usize, dj: usize) -> usize {
        let mut j = 0;
        let mut i = 0;
        let mut count = 0;
        while let Some(v) = self.get(i, j) {
            if v {
                count += 1;
            }
            i += di;
            j += dj;
        }
        count
    }
}

fn input() -> Input {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();
    let mut data = String::new();
    stdin.read_to_string(&mut data).expect("An I/O error occurred");
    Input::parse(data)
}

fn part_a(input: &Input) -> usize {
    input.walk(1, 3)
}

fn part_b(input: &Input) -> usize {
    input.walk(1, 1) * input.walk(1, 3)
        * input.walk(1, 5) * input.walk(1, 7)
        * input.walk(2, 1)
}

fn main() {
    let data = input();
    let a_soln = part_a(&data);
    let b_soln = part_b(&data);
    println!("Part a: {}, part b: {}", a_soln, b_soln);
}
