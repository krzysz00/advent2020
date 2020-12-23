#!/usr/bin/env python3

from z3 import *
import fileinput
import numpy as np

def borders(tile):
    top = tuple(tile[0,:])
    bot = tuple(tile[-1,:])
    right = tuple(tile[:,-1])
    left = tuple(tile[:,0])
    return [top, right, bot, left, top[::-1], right[::-1], bot[::-1], left[::-1]]

def convertor(f, status="unknown", name="benchmark", logic=""):
    v = (Ast * 0)()
    if isinstance(f, Solver) or inisntance(f, SolverFor):
        a = f.assertions()
        if len(a) == 0:
            f = BoolVal(True)
        else:
            f = And(*a)
        return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())

class SMTEncode:
    def __init__(self, input):
        self.tiles = input
        self.n = int(np.sqrt(len(input)))
        if self.n * self.n != len(self.tiles):
            raise ArgumentError("Can't make tiles into a square");
        #self.solver = Solver()
        self.solver = Then('propagate-values', 'injectivity', 'occf', 'simplify', 'solve-eqs',
                           'elim-uncnstr', 'reduce-args', 'propagate-values',
                          'psmt').solver()

    def setup_problem_a(self):
        self.Position, position_refs = EnumSort("Position", [f"p_{i},{j}" for j in range(self.n)
                                                             for i in range(self.n)])
        self.positions = dict(zip(((i, j) for j in range(self.n) for i in range(self.n)),
                                  position_refs))

        tile_list = list(self.tiles.items())
        self.Tile, tile_refs = EnumSort("Tile", [f"t{k}" for k, v in tile_list])
        self.tile_ref_to_id = {v: e[0] for v, e in zip(tile_refs, tile_list)}
        self.id_to_tile_ref = {v: k for k, v, in self.tile_ref_to_id.items()}

        border_map = {k: borders(v) for k, v, in self.tiles.items()}
        borders_list = list(set(v for d in border_map.values() for v in d))
        self.Border, self.border_refs = EnumSort("Border", [f"b{i}" for i in range(len(borders_list))])
        self.border_ref_map = dict(zip(borders_list, self.border_refs))

        border_types = ["top", "right", "bot", "left"]
        self.border_fns = [Function(f"border_{t}", self.Tile, self.Border) for t in border_types]

        # Symmetries cribbed from http://facstaff.cbu.edu/wschrein/media/M402%20Notes/M402C1.pdf
        # Note, on the original, top and bottom are left->right, left and right are top->bottom
        permutations = [("id", [0, 1, 2, 3]), # id
                        ("r90", [1, 2 + 4, 3, 0 + 4]), # 90 degrees (+4 is orientation flip)
                        ("r180", [2 + 4, 3 + 4, 0 + 4, 1 + 4]),
                        ("r270", [3 + 4, 0, 1 + 4, 2]),
                        ("fH", [2, 1 + 4, 0, 3 + 4]),
                        ("fV", [0 + 4, 3, 2 + 4, 1]),
                        ("fTL", [3, 2, 1, 0]),
                        ("fTR", [1 + 4, 0 + 4, 3 + 4, 2 + 4])
        ]

        # Permutations
        for id, old_borders in border_map.items():
            tile_sym = self.id_to_tile_ref[id]
            self.solver.add(Or([And([f(tile_sym) == self.border_ref_map[old_borders[perm[i]]]
                                     for i, f in enumerate(self.border_fns)])
                                for name, perm in permutations]))

        self.tile_at = Function("tile_at", self.Position, self.Tile)
        # Position constraints
        btfns = dict(zip(border_types, self.border_fns))
        for i in range(self.n):
            for j in range(self.n):
                me = self.tile_at(self.positions[(i, j)])
                if i != 0:
                    self.solver.add(btfns["top"](me) ==
                                    btfns["bot"](self.tile_at(self.positions[(i - 1, j)])))
                if i + 1 != self.n:
                    self.solver.add(btfns["bot"](me) ==
                                    btfns["top"](self.tile_at(self.positions[(i + 1, j)])))
                if j != 0:
                    self.solver.add(btfns["left"](me) ==
                                    btfns["right"](self.tile_at(self.positions[(i, j - 1)])))
                if j + 1 != self.n:
                    self.solver.add(btfns["right"](me) ==
                                    btfns["left"](self.tile_at(self.positions[(i, j + 1)])))


        # Distinctness
        t = Const('t', self.Tile);
        self.position_of = Function("position_of", self.Tile, self.Position);
        self.solver.add(ForAll(t, self.tile_at(self.position_of(t)) == t))

        print(convertor(self.solver))

    def solve_a(self):
        print(self.solver.check())
        m = self.solver.model()
        n_max = self.n - 1
        corner_vals = [self.positions[l] for l in
                       [(0, 0), (0, n_max), (n_max, 0), (n_max, n_max)]]
        corner_tile_vals = [m.eval(self.tile_at(p)) for p in corner_vals]
        print(corner_tile_vals)
        return np.prod([self.tile_ref_to_id[v] for v in corner_tile_vals])

def part_a(input):
    encoder = SMTEncode(input)
    encoder.setup_problem_a()
    return encoder.solve_a()

def read_input():
    current = []
    current_id = None
    n = None
    ret = dict()
    # Note, we very insistently assume Unix line endings here
    for line in fileinput.input():
        if line.startswith("Tile "):
            if current_id is not None:
                raise ArgumentError("Previous tile not closed")
            current_id = int(line[len("Tile "):-2])
            current = []
        elif line == "\n" or len(line) == 0:
            if current_id is None or n is None:
                raise ArgumentError("Didn't parse a literal")
            if current_id in ret:
                raise(ArgumentError(f"Duplicate ID {current_id}"))
            ret[current_id] = np.array(current).reshape((-1, n))
            current = []
            current_id = None
            n = None
        else:
            for c in line[:-1]:
                if c == '.':
                    current.append(False)
                elif c == '#':
                    current.append(True)
                else:
                    raise ArgumentError(f"Unknown character in line {c}")
            if n is None:
                n = len(line) - 1
            elif n != (len(line) - 1):
                raise ArgumentError(f"Jagged line lengths: {n} != {len(line)}")
    if current_id is not None and n is not None:
        ret[current_id] = np.array(current).reshape((-1, n))
    return ret

if __name__ == '__main__':
    input = read_input()
    soln_a = part_a(input)
    print(f"Part a: {soln_a}")
