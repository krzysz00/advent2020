#!/usr/bin/env python3

import fileinput
import io
import numpy as np

def borders(tile):
    top = tuple(tile[0,:])
    bot = tuple(tile[-1,:])
    right = tuple(tile[:,-1])
    left = tuple(tile[:,0])
    return [top, right, bot, left, top[::-1], right[::-1], bot[::-1], left[::-1]]

class PrologEncode:
    def __init__(self, input):
        self.tiles = input
        self.n = int(np.sqrt(len(input)))
        if self.n * self.n != len(self.tiles):
            raise ArgumentError("Can't make tiles into a square");

    def encode_problem_a(self):
        out = io.StringIO()
        tile_atoms = {k: f"t{k}" for k in self.tiles.keys()}
        borders_map = {k: borders(v) for k, v, in self.tiles.items()}

        borders_list = list(set(v for d in borders_map.values() for v in d))
        border_atoms = {v: f"b{i}" for i, v in enumerate(borders_list)}

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

        for id, atom in tile_atoms.items():
            print(f"tile_id({atom}, {id}).", file=out)

        for atom in tile_atoms.values():
            print(f"tile({atom}).", file=out)

        for id, atom in tile_atoms.items():
            for name, perm in permutations:
                atoms = [border_atoms[borders_map[id][perm[i]]] for i in range(len(perm))]
                body = ", ".join(f"{v} = {a}" for v, a in zip(["T", "R", "B", "L"], atoms))
                print(f"borders({atom}, T, R, B, L) :- {body}.", file=out)

        max_n = self.n - 1
        print(f"valid(P0_0, P0_{max_n}, P{max_n}_0, P{max_n}_{max_n}) :-", file=out)
        print("  permutation([{}], [{}]),".format(
            ", ".join(tile_atoms.values()),
            ", ".join(f"P{i}_{j}" for i in range(self.n) for j in range(self.n))),
              file=out)
        for i in range(self.n):
            for j in range(self.n):
                print(f"  borders(P{i}_{j}, T{i}_{j}, R{i}_{j}, B{i}_{j}, L{i}_{j}),", file=out)
                if i != 0:
                    print(f"  T{i}_{j} = B{i - 1}_{j},", file=out)
                if j != 0:
                    print(f"  L{i}_{j} = R{i}_{j - 1},", file=out)
        print("  true.", file=out)

        print("""times(X, Y, Z) :- Z is X * Y.
part_a(Ans) :- valid(Tl, Tr, Bl, Br),
               maplist(tile_id, [Tl, Tr, Bl, Br], Ids),
               foldl(times, Ids, 1, Ans).""", file=out)
        ret = out.getvalue()
        out.close()
        return ret

def part_a(input):
    encoder = PrologEncode(input)
    prolog = encoder.encode_problem_a()
    print(prolog)

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
    #print(f"Part a: {soln_a}")
