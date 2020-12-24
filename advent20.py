#!/usr/bin/env python3

import fileinput
import io
import tempfile
import re
import subprocess
import os.path
import numpy as np

MONSTER_MASK = np.array([
    [np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,np.nan,True,np.nan],
    [True,np.nan,np.nan,np.nan,np.nan,True,True,np.nan,np.nan,np.nan,np.nan,True,True,np.nan,np.nan,np.nan,np.nan,True,True,True],
    [np.nan,True,np.nan,np.nan,True,np.nan,np.nan,True,np.nan,np.nan,True,np.nan,np.nan,True,np.nan,np.nan,True,np.nan,np.nan,np.nan]])

(MASK_M, MASK_N) = MONSTER_MASK.shape

MONSTER_MASK_LOCS = MONSTER_MASK == True

def borders(tile):
    top = tuple(tile[0,:])
    bot = tuple(tile[-1,:])
    right = tuple(tile[:,-1])
    left = tuple(tile[:,0])
    return [top, right, bot, left, top[::-1], right[::-1], bot[::-1], left[::-1]]

def permute(tile, perm):
    if perm == "id":
        return tile
    elif perm == "r90":
        return np.rot90(tile)
    elif perm == "r180":
        return np.rot90(tile, k=2)
    elif perm == "r270":
        return np.rot90(tile, k=3)
    elif perm == "fh":
        return np.flipud(tile)
    elif perm == "fv":
        return np.fliplr(tile)
    elif perm == "ftl":
        return np.rot90(np.fliplr(tile))
    elif perm == "ftr":
        return np.rot90(np.fliplr(tile), k=3)
    else:
        raise ArgumentError("Unknown permutation: {}", perm)

def test_monster_mask(array, i0, j0, point_set):
    if not np.array_equal(MONSTER_MASK[MONSTER_MASK_LOCS],
                          (array[i0:i0+MASK_M,j0:j0+MASK_N])[MONSTER_MASK_LOCS]):
        return False
    for i in range(MASK_M):
        for j in range(MASK_N):
            if MONSTER_MASK[i, j] == True:
                if ((i0 + i, j0 + j)) in point_set:
                    print("Duplicate point: {{i0 + i, j0 + j}}")
                point_set.add((i0 + i, j0 + j))
    return True

class PrologEncode:
    def __init__(self, input):
        self.tiles = input
        self.n = int(np.sqrt(len(input)))
        if self.n * self.n != len(self.tiles):
            raise ArgumentError("Can't make tiles into a square");
        self.perms = None
        self.tile_ids = None

    def prolog_write_script(self, out):
        tile_atoms = {k: f"t{k}" for k in self.tiles.keys()}
        borders_map = {k: borders(v) for k, v, in self.tiles.items()}

        # Symmetries cribbed from http://facstaff.cbu.edu/wschrein/media/M402%20Notes/M402C1.pdf
        # Note, on the original, top and bottom are left->right, left and right are top->bottom
        permutations = [("id", [0, 1, 2, 3]), # id
                        ("r90", [1, 2 + 4, 3, 0 + 4]),
                        ("r180", [2 + 4, 3 + 4, 0 + 4, 1 + 4]),
                        ("r270", [3 + 4, 0, 1 + 4, 2]),
                        ("fh", [2, 1 + 4, 0, 3 + 4]),
                        ("fv", [0 + 4, 3, 2 + 4, 1]),
                        ("ftl", [3, 2, 1, 0]),
                        ("ftr", [1 + 4, 0 + 4, 3 + 4, 2 + 4])
                ]

        print(":- discontiguous right_of/4, below_of/4.", file=out)
        for id, atom in tile_atoms.items():
            print(f"tile_id({atom}, {id}).", file=out)

        for atom in tile_atoms.values():
            print(f"tile({atom}).", file=out)

        for id1, atom1 in tile_atoms.items():
            for id2, atom2 in tile_atoms.items():
                if id1 == id2:
                    continue
                for name1, perm1 in permutations:
                    for name2, perm2 in permutations:
                        if borders_map[id1][perm1[3]] == borders_map[id2][perm2[1]]:
                            print(f"right_of({atom1}, {name1}, {atom2}, {name2}).", file=out)
                        if borders_map[id1][perm1[0]] == borders_map[id2][perm2[2]]:
                            print(f"below_of({atom1}, {name1}, {atom2}, {name2}).", file=out)

        print("""\nis_permutation(Xs, Ys) :-
  msort(Xs, Sorted),
  msort(Ys, Sorted).""", file=out)
        print("\nvalid([{}]) :-".format(
            ", ".join(f"[P{i}_{j}, Perm{i}_{j}]"
                      for i in range(self.n) for j in range(self.n))), file=out)

        for i in range(self.n):
            for j in range(self.n):
                if i != 0:
                    print(f"  below_of(P{i}_{j}, Perm{i}_{j}, P{i - 1}_{j}, Perm{i - 1}_{j}),", file=out)
                if j != 0:
                    print(f"  right_of(P{i}_{j}, Perm{i}_{j}, P{i}_{j - 1}, Perm{i}_{j - 1}),", file=out)
        print("  is_permutation([{}], [{}]).".format(
            ", ".join(tile_atoms.values()),
            ", ".join(f"P{i}_{j}" for i in range(self.n) for j in range(self.n))
        ), file=out)

        print("""print_result(Res) :- format("t: ~a perm: ~a~n", Res).
        main :- valid(Positions), !, maplist(print_result, Positions), halt.
        :- initialization main.""", file=out)

    def prolog_solve(self):
        regex = re.compile("^t: t(\d+) perm: (\w+)$")
        with tempfile.TemporaryDirectory() as tempdir:
            filename = os.path.join(tempdir, "queries.pl")
            with open(filename, 'w') as out:
                self.prolog_write_script(out)
            output = subprocess.run(["swipl", "-q", "-s", filename],
                                    capture_output=True, check=True,
                                    encoding='UTF-8', errors='strict')
            perms = []
            tile_ids = []
            for line in output.stdout.splitlines():
                match = regex.match(line)
                if match is None:
                    raise ValueError(f"Unexpected script output: {line}")
                tile_ids.append(int(match[1]))
                perms.append(match[2])
            self.perms = np.array(perms).reshape((self.n, self.n))
            self.tile_ids = np.array(tile_ids).reshape((self.n, self.n))

    def part_a(self):
        if self.tile_ids is None:
            raise ArgumentError("Didn't solve the problem first")
        return (self.tile_ids[0,0] * self.tile_ids[0, -1] *
                self.tile_ids[-1,0] * self.tile_ids[-1,-1])

    def part_b_image(self):
        if self.tile_ids is None:
            raise ArgumentError("Prolag problem not solved first")
        return np.block([[permute(self.tiles[i], p)[1:-1,1:-1] for i, p in zip(i_s, p_s)]
                         for i_s, p_s in zip(self.tile_ids.tolist(), self.perms.tolist())])

    def part_b(self):
        raw_image = self.part_b_image()
        shape = raw_image.shape
        if shape[0] != shape[1]:
            raise ValueError("Non-square shape somehow")
        n = shape[0]
        for perm in ["id", "r90", "r180", "r270", "fh", "fv", "ftl", "ftr"]:
            image = permute(raw_image, perm)
            assert(image.shape == shape)

            sea_monster_points = set()
            for i0 in range((n - MASK_M) + 1):
                for j0 in range((n - MASK_N) + 1):
                    test_monster_mask(image, i0, j0, sea_monster_points)
            if len(sea_monster_points) != 0:
                return sum(1 for i in range(n) for j in range(n)
                           if image[i, j] == True
                           and ((i, j) not in sea_monster_points))
        raise ValueError("No sea monsters in image at all")

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
    encoder = PrologEncode(input)
    encoder.prolog_solve()
    part_a = encoder.part_a()
    print("Part a:", part_a)
    part_b = encoder.part_b()
    print("Part b:", part_b)
