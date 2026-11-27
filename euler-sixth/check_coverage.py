"""Independently count the lattice points and cross-check a smaller search."""
from collections import defaultdict
from bisect import bisect_left
from math import gcd
import argparse

from search import MODULUS, candidate_pairs, two_sixths, unit_roots


def floor_sum(n, m, a, b):
    """Return the sum of floor((a*i+b)/m) for 0 <= i < n."""
    total = 0
    while n:
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        total += qa*n*(n-1)//2 + qb*n
        top = a*n+b
        if top < m:
            break
        n, b = divmod(top, m)
        m, a = a, m
    return total


def count_pairs(bound):
    total = 0
    roots = unit_roots()
    assert len(roots) == len(set(roots)) == 144
    assert all(pow(r, 6, MODULUS) == 1 for r in roots)
    for r in roots:
        # Count 0 < a < z with a = r*z modulo M at z=d,2d,... .
        # Inclusion-exclusion removes z divisible by 2, 3 or 7.
        for d, sign in ((1,1),(2,-1),(3,-1),(7,-1),(6,1),(14,1),(21,1),(42,-1)):
            n = bound // d
            upper, lower = (1-r)*d, -r*d
            total += sign*(floor_sum(n, MODULUS, upper, upper-1)
                           - floor_sum(n, MODULUS, lower, lower))
    return total


def check_small(bound=1_000_000):
    # Direct modular exponentiation, without roots of unity or lattice reduction.
    seen = defaultdict(list)
    direct = set()
    for z in range(1, bound+1):
        if gcd(z, 42) == 1:
            earlier = seen[pow(z, 6, MODULUS)]
            direct.update((z, a) for a in earlier)
            earlier.append(z)
    listed = [p for r in unit_roots() for p in candidate_pairs(r, bound)]
    assert len(listed) == len(direct) == count_pairs(bound)
    assert set(listed) == direct
    print(f'{len(direct):,} candidate pairs agree individually through {bound:,}')
    # A separate exact two-pointer search, without the modular filters or wheel.
    powers = [i**6 for i in range(bound//42 + 1)]
    for z, a in direct:
        target = (z**6-a**6)//MODULUS
        lo, hi = 1, bisect_left(powers, target)-1
        while lo <= hi:
            total = powers[lo] + powers[hi]
            if total == target:
                raise ValueError(f'Positive witness {(a, 42*lo, 42*hi, z)}')
            if total < target:
                lo += 1
            else:
                hi -= 1
    print(f'Independent two-pointer search found no witness through {bound:,}')


def check_complements():
    powers = [i**6 for i in range(16385)]
    index = {v: i for i, v in enumerate(powers) if i}
    for u in (1, 2, 7, 13, 31, 42, 64, 109, 128, 729, 7657, 16384):
        for v in (u, 16384):
            target = powers[u] + powers[v]
            pair = two_sixths(target, powers, index)
            assert pair is not None
            a, b = pair
            assert 1 <= a <= b and powers[a] + powers[b] == target
    assert two_sixths(1, powers, index) is None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    args = parser.parse_args()
    if args.bound < 1:
        parser.error('bound must be positive')
    check_complements()
    check_small()
    print(f'{count_pairs(args.bound):,} eligible pairs through {args.bound:,} by floor sums')
