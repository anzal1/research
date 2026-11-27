"""Try one repeated pair with a single summand coprime to 42, through a given z."""
from bisect import bisect_left
from collections import defaultdict
from math import gcd
import argparse

from search import FILTERS, sixths_mod, two_sixths


def search(bound):
    powers = [n**6 for n in range(bound//42+1)]
    index = {p:i for i,p in enumerate(powers) if i}
    modulus = 42**6
    filters = []
    for q in FILTERS:
        sixths = sixths_mod(q)
        filters.append((q, {(i+j)%q for i in sixths for j in sixths}))
    seen = defaultdict(list)
    pairs = probes = 0
    for z in range(1, bound+1):
        if gcd(z,42) != 1:
            continue
        key = pow(z,6,modulus)
        for a in seen[key]:
            pairs += 1
            target = (z**6-a**6)//modulus
            for w in range(1,bisect_left(powers,(target+1)//2)):
                left = target-2*powers[w]
                if any(left%q not in residues for q,residues in filters):
                    continue
                probes += 1
                found = two_sixths(left,powers,index)
                if found:
                    u,v=found
                    summands=[a,42*u,42*v,42*w,42*w]
                    assert min(summands)>0 and sum(x**6 for x in summands)==z**6
                    return pairs,probes,(summands,z)
        seen[key].append(z)
    return pairs,probes,None


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bound',type=int)
    args=parser.parse_args()
    if args.bound<1:
        parser.error('bound must be positive')
    pairs,probes,witness=search(args.bound)
    print(f'one repeated pair, coprime singleton, z <= {args.bound}: {pairs} eligible pairs, {probes} complementary searches, witness={witness}')
