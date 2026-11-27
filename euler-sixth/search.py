"""Exact search for a^6 + 2 b^6 + 2 c^6 = z^6 with positive bases."""
import argparse
from bisect import bisect_right
from functools import lru_cache
from itertools import product
from math import gcd

FACTORS = (128, 729, 117649)
MODULUS = 2 * 42**6
FILTERS = (8, 9, 7, 13, 19, 31, 37, 43, 61, 73, 109, 49, 64, 81, 169)
WHEEL_FACTORS = (8, 9, 7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109)


def unit_roots():
    factors = [[r for r in range(q) if pow(r, 6, q) == 1] for q in FACTORS]
    coefficients = [(MODULUS // q) * pow(MODULUS // q, -1, q) for q in FACTORS]
    return [sum(r * c for r, c in zip(row, coefficients)) % MODULUS
            for row in product(*factors)]


def reduced_basis(root):
    # Every (z, a) in this lattice satisfies a = root*z modulo MODULUS.
    u, v = (1, root), (0, MODULUS)
    while True:
        norm = u[0]**2 + u[1]**2
        dot = u[0]*v[0] + u[1]*v[1]
        if 2 * abs(dot) <= norm:
            return u, v
        q = (2*dot + norm) // (2*norm)
        w = (v[0] - q*u[0], v[1] - q*u[1])
        if w[0]**2 + w[1]**2 >= norm:
            return u, w
        u, v = w, u


def ceil_div(a, b):
    return -((-a) // b)


def candidate_pairs(root, bound):
    u, v = reduced_basis(root)
    det = u[0]*v[1] - u[1]*v[0]
    if det < 0:
        v = (-v[0], -v[1])
        det = -det
    assert det == MODULUS
    # Points are m*u+n*v. Bound n by its extrema on the enclosing triangle.
    vertices = (0, -u[1]*bound, (u[0]-u[1])*bound)
    for n in range(ceil_div(min(vertices), det), max(vertices)//det + 1):
        lows, highs = [], []
        for slope, offset in ((u[0], n*v[0]), (u[1], n*v[1]),
                              (u[0]-u[1], n*(v[0]-v[1]))):
            # Impose 1 <= z, a, z-a <= bound, including all triangle edges.
            if slope > 0:
                lows.append(ceil_div(1-offset, slope))
                highs.append((bound-offset)//slope)
            elif slope < 0:
                lows.append(ceil_div(bound-offset, slope))
                highs.append((1-offset)//slope)
            elif not 1 <= offset <= bound:
                break
        else:
            for m in range(max(lows), min(highs) + 1):
                z, a = m*u[0]+n*v[0], m*u[1]+n*v[1]
                if gcd(z, 42) == 1:
                    yield z, a


def sixths_mod(q):
    return {pow(i, 6, q) for i in range(q)}


@lru_cache(maxsize=None)
def allowed_bases(q, target_mod):
    sixths = sixths_mod(q)
    return tuple(i for i in range(q) if (target_mod - pow(i, 6, q)) % q in sixths)


def two_sixths(target, powers, index):
    """Find 1 <= u <= v with u^6 + v^6 = target, given a sufficient power table."""
    stop = bisect_right(powers, target // 2)
    rows = [(q, allowed_bases(q, target % q)) for q in WHEEL_FACTORS]
    if any(not row for _, row in rows):
        return None
    # Use the most selective moduli first. The choice affects only runtime.
    rows.sort(key=lambda item: 10000 * len(item[1]) // item[0])
    period, slots = 1, [0]
    for q, allowed in rows:
        if period*q > max(64, 2*stop):
            continue
        inverse = pow(period, -1, q)
        slots = [s + period*((r-s)*inverse % q) for s in slots for r in allowed]
        period *= q
    for r in slots:
        for u in range(r or period, stop, period):
            v = index.get(target - powers[u])
            if v is not None:
                return u, v
    return None


def search(bound):
    filters = []
    for q in FILTERS:
        residues = sixths_mod(q)
        filters.append((q, {(x+y) % q for x in residues for y in residues}))
    powers = [i**6 for i in range(bound//42 + 1)]
    index = {v: i for i, v in enumerate(powers) if i}
    pairs = survivors = 0
    for root in unit_roots():
        for z, a in candidate_pairs(root, bound):
            diff = z**6 - a**6
            assert diff % MODULUS == 0
            pairs += 1
            target = diff // MODULUS
            if any(target % q not in ok for q, ok in filters):
                continue
            survivors += 1
            pair = two_sixths(target, powers, index)
            if pair is not None:
                u, v = pair
                b, c = 42*u, 42*v
                assert 0 < a < z and 0 < b <= c < z
                assert a**6 + 2*b**6 + 2*c**6 == z**6
                return pairs, survivors, (a, b, c, z)
    return pairs, survivors, None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    bound = parser.parse_args().bound
    if bound < 1:
        parser.error('bound must be positive')
    pairs, survivors, witness = search(bound)
    print(f'z <= {bound:,}; {pairs:,} eligible (z,a) pairs; '
          f'{survivors:,} passed modular filters; witness = {witness}')
