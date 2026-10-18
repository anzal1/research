#!/usr/bin/env python3
"""Check the 14 seed codes in seeds.magma without Magma.

For each seed D = [n, M, d]_9 it checks:
  1. the M rows are linearly independent (dimension M),
  2. H H^dagger = 0 over GF(9) (Hermitian self-orthogonal, so hull dimension = M),
  3. the minimum Hamming distance equals the claimed d (exact, all 9^M codewords).

GF(9) = GF(3)[w] / (w^2 + 1). Element a + b*w is stored as the integer a + 3*b,
the same encoding as seeds.magma. Needs numpy.
"""
import re, sys, itertools
import numpy as np

ADD = np.zeros((9, 9), np.uint8)
MUL = np.zeros((9, 9), np.uint8)
CONJ = np.zeros(9, np.uint8)
for x in range(9):
    a, b = x % 3, x // 3
    CONJ[x] = a + 3 * ((-b) % 3)          # conjugation x -> x^3 sends w to -w
    for y in range(9):
        c, d = y % 3, y // 3
        ADD[x, y] = (a + c) % 3 + 3 * ((b + d) % 3)
        MUL[x, y] = (a * c - b * d) % 3 + 3 * ((a * d + b * c) % 3)   # w^2 = -1

def hso(H):
    M = len(H)
    for i in range(M):
        for j in range(i, M):
            s = 0
            for u, v in zip(H[i], H[j]):
                s = ADD[s, MUL[u, CONJ[v]]]
            if s:
                return False
    return True

def min_weight(H):
    """Exact minimum weight. Returns 0 if the rows are dependent."""
    H = np.array(H, np.uint8)
    M, n = H.shape
    inner, outer = H[-min(M, 6):], H[:M - min(M, 6)]
    scal = np.arange(9, dtype=np.uint8)
    S = np.zeros((1, n), np.uint8)
    for row in inner:
        scaled = MUL[scal[:, None], row[None, :]]                  # (9, n)
        S = ADD[S[:, None, :], scaled[None, :, :]].reshape(-1, n)  # all combinations
    best = n + 1
    for coefs in itertools.product(range(9), repeat=len(outer)):
        v = np.zeros(n, np.uint8)
        for c, row in zip(coefs, outer):
            v = ADD[v, MUL[c, row]]
        w = (ADD[S, v[None, :]] != 0).sum(axis=1)
        if not any(coefs):
            w = w[1:]                       # skip the all-zero combination
        m = int(w.min())
        if m == 0:
            return 0
        best = min(best, m)
    return best

def parse(path):
    text = open(path).read()
    for m in re.finditer(r'VerifySeed\("(\w+)",\s*(\d+),\s*(\d+),\s*(\d+),\s*\[(.*?)\]\);', text, re.S):
        name, n, M, d, body = m.group(1), int(m.group(2)), int(m.group(3)), int(m.group(4)), m.group(5)
        rows = [[int(x) for x in r.split(",")] for r in re.findall(r'\[([0-9,\s]+)\]', body)]
        yield name, n, M, d, rows

def main(path="seeds.magma"):
    ok_all, count = True, 0
    for name, n, M, d, rows in parse(path):
        count += 1
        shape_ok = len(rows) == M and all(len(r) == n for r in rows)
        h = shape_ok and hso(rows)
        mw = min_weight(rows) if shape_ok else -1
        ok = shape_ok and h and mw == d
        ok_all &= ok
        print(f"{name:10} [{n},{M},{d}]_9  hermitian_self_orthogonal={h}  min_distance={mw}  {'OK' if ok else 'FAIL'}")
    print(f"\n{count} seeds checked: {'ALL OK' if ok_all and count == 14 else 'FAILURE'}")
    return 0 if ok_all and count == 14 else 1

if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:]))
