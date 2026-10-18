#!/usr/bin/env python3
"""Check the 16 degenerate (impure) k = 1 qutrit codes by exhaustive enumeration.

Each code is built from the repetition code [N, 1, N]_9 plus ell blocks carrying the
stabilizer (1, 1, 1). For each one this computes, from scratch over GF(3):
s (stabilizer size), c (ebits), k (logical qutrits), the degenerate distance
d = min symplectic weight over S^perp minus S, and the pure distance.
It then checks n, k, c, d against the claimed table entry. Standard library only.
Verifier logic written by the Fable review pass, extended here to all 16 cells.
"""
import itertools, sys

def gf9_mul(x, y):
    ax, bx, ay, by = x % 3, x // 3, y % 3, y // 3
    return (ax*ay + 2*bx*by) % 3 + 3*((ax*by + bx*ay) % 3)

def to_f3(row9, n):
    return [v % 3 for v in row9] + [v // 3 for v in row9]

def rank_f3(rows):
    M = [r[:] for r in rows]; r = 0
    if not M: return 0
    cols = len(M[0])
    for c in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 if M[r][c] == 1 else 2
        M[r] = [(x*inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(a - f*b) % 3 for a, b in zip(M[i], M[r])]
        r += 1
    return r

def nullspace_f3(rows, cols):
    M = [r[:] for r in rows]; piv = []; r = 0
    for c in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = 1 if M[r][c] == 1 else 2
        M[r] = [(x*inv) % 3 for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(a - f*b) % 3 for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for f in free:
        v = [0]*cols; v[f] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][f]) % 3
        basis.append(v)
    return basis

def symp(a, b, n):
    return (sum(a[i]*b[n+i] for i in range(n)) - sum(a[n+i]*b[i] for i in range(n))) % 3

def swt(v, n):
    return sum(1 for i in range(n) if v[i] or v[n+i])

def check(name, D9, n):
    # D9: F9 generator rows (normalizer side). F3 rows: psi(h), psi(w h)
    rows = []
    for h in D9:
        rows.append(to_f3(h, n))
        rows.append(to_f3([gf9_mul(3, x) for x in h], n))  # 3 encodes w
    dimN = rank_f3(rows)
    # S = symplectic dual of span(rows): vectors s with <row, s>_s = 0  <=> rows J s^T = 0
    rowsJ = [[(-r[n+j]) % 3 for j in range(n)] + [r[j] for j in range(n)] for r in rows]
    S = nullspace_f3(rowsJ, 2*n)
    s = rank_f3(S)
    Om = [[symp(a, b, n) for b in S] for a in S]
    c2 = rank_f3(Om); c = c2 // 2; k = n - s + c
    # enumerate S^perp = span(rows) (dim dimN) over F3
    basis = []
    # independent subset of rows
    cur = []
    for r in rows:
        if rank_f3(cur + [r]) > len(cur): cur.append(r)
    basis = cur
    dmin_all, dmin_noniso, iso_cnt = None, None, 0
    for coeffs in itertools.product(range(3), repeat=len(basis)):
        if not any(coeffs): continue
        v = [0]*(2*n)
        for cf, b in zip(coeffs, basis):
            if cf:
                v = [(x + cf*y) % 3 for x, y in zip(v, b)]
        w = swt(v, n)
        dmin_all = w if dmin_all is None else min(dmin_all, w)
        iso = all(symp(v, sv, n) == 0 for sv in S)  # v in S^perp always; v in S iff orth to S^perp... use: v in S <=> symp(v, x)=0 for all x in S^perp
        iso = all(symp(v, b, n) == 0 for b in basis)
        if iso:
            iso_cnt += 1
        else:
            dmin_noniso = w if dmin_noniso is None else min(dmin_noniso, w)
    return n, k, c, dmin_noniso, dmin_all

u0 = [0, 4, 8]  # (0, 1+w, 2+2w)
def build(N, ell, norm_fix):
    # base b of length N with sum of norms != 0 mod 3
    b = [1]*N
    if N % 3 == 0: b[0] = 4  # norm 2 -> total N-1+2 = N+1
    # replace coords 0..ell-1 by b_i * u0, append e-blocks
    bp = []
    es = []
    pos = 0
    blocks = []
    for i in range(N):
        if i < ell:
            bp += [gf9_mul(b[i], x) for x in u0]; blocks.append(pos); pos += 3
        else:
            bp.append(b[i]); pos += 1
    n = len(bp)
    for p in blocks:
        e = [0]*n; e[p:p+3] = [1, 1, 1]; es.append(e)
    return [bp] + es, n

# (n, k, c, d) claimed, with (N, ell)
CELLS = [((12,1,9,11),(10,1)), ((13,1,8,11),(9,2)), ((13,1,10,12),(11,1)), ((14,1,9,12),(10,2)),
         ((14,1,11,13),(12,1)), ((15,1,10,13),(11,2)), ((15,1,12,14),(13,1)), ((16,1,11,14),(12,2)),
         ((16,1,13,15),(14,1)), ((17,1,12,15),(13,2)), ((17,1,14,16),(15,1)), ((18,1,15,17),(16,1)),
         ((19,1,14,17),(15,2)), ((19,1,16,18),(17,1)), ((20,1,15,18),(16,2)), ((20,1,17,19),(18,1))]

if __name__ == "__main__":
    bad = 0
    for (n0,k0,c0,d0),(N,ell) in CELLS:
        D9, n = build(N, ell, True)
        n1,k1,c1,d1,dp = check(f"N={N} ell={ell}", D9, n)
        ok = (n1,k1,c1,d1) == (n0,k0,c0,d0)
        bad += not ok
        print(f"[[{n1},{k1},{d1};{c1}]]_3  pure distance {dp}  claimed [[{n0},{k0},{d0};{c0}]]_3  {'OK' if ok else 'FAIL'}")
    print(f"\n16 degenerate codes checked: {'ALL OK' if bad == 0 else str(bad) + ' FAILED'}")
    sys.exit(1 if bad else 0)
