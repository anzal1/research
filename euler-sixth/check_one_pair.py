"""Cross-check the bounded one-pair search with sorted residues and direct lookup."""
from bisect import bisect_right
from itertools import combinations, groupby
from math import gcd
import argparse


def check(bound):
    modulus = 42**6
    rows = sorted((pow(n, 6, modulus), n) for n in range(1, bound+1) if gcd(n, 42) == 1)
    powers = [n**6 for n in range(1, bound//42+1)]
    lookup = set(powers)
    filters = []
    for m in (13, 19, 31, 37, 43, 61, 73, 109, 169, 8, 9, 7, 49, 64, 81):
        residues = {pow(n, 6, m) for n in range(m)}
        filters.append((m, {(x+y) % m for x in residues for y in residues}))
    pairs = probes = 0
    for _, group in groupby(rows, key=lambda row: row[0]):
        for (_, a), (_, z) in combinations(group, 2):
            pairs += 1
            target = (z**6-a**6)//modulus
            for p in powers:
                remaining = target-2*p
                if remaining < 2:
                    break
                if any(remaining % m not in sums for m, sums in filters):
                    continue
                probes += 1
                for i in range(bisect_right(powers, remaining//2)):
                    if remaining-powers[i] in lookup:
                        return pairs, probes, (a,z,p,powers[i],remaining-powers[i])
    return pairs, probes, None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound', type=int)
    args = parser.parse_args()
    pairs, probes, witness = check(args.bound)
    print(f'direct lookup through {args.bound}: {pairs} eligible pairs, {probes} complementary searches, witness={witness}')
