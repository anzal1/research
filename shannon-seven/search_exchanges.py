"""Find an improved five-letter code by replacing up to five appendix words."""
from collections import defaultdict
from itertools import combinations, product
from pathlib import Path
import argparse

from check_projection import close


def extension(pool, need):
    if need == 0:
        return []
    for i, word in enumerate(pool):
        if len(pool) - i < need:
            break
        compatible = [w for w in pool[i + 1:] if not close(word, w)]
        tail = extension(compatible, need - 1)
        if tail is not None:
            return [word, *tail]
    return None


def search(max_removed):
    code = [tuple(map(int, w)) for w in
            Path(__file__).with_name('polak_schrijver.txt').read_text().split()]
    assert len(set(code)) == 367 and all(not close(a,b) for a,b in combinations(code,2))
    blockers = defaultdict(list)
    shifts = list(product((-1, 0, 1), repeat=5))
    for i, word in enumerate(code):
        for offset in shifts:
            other = tuple((x+y) % 7 for x,y in zip(word, offset))
            blockers[other].append(i)
    assert len(blockers) == 7**5
    seed = set(code)
    groups = defaultdict(list)
    for word, indices in blockers.items():
        if word not in seed and len(indices) <= max_removed:
            groups[frozenset(indices)].append(word)
    # A smallest improving exchange has a connected blocker hypergraph.
    # Otherwise at least one component adds more words than it removes.
    by_vertex = defaultdict(list)
    for edge in groups:
        for i in edge:
            by_vertex[i].append(edge)
    queue = list(groups)
    seen = set(queue)
    for edge in queue:
        for i in edge:
            for neighbor in by_vertex[i]:
                joined = edge | neighbor
                if len(joined) <= max_removed and joined not in seen:
                    seen.add(joined)
                    queue.append(joined)
    counts = [0]*(max_removed+1)
    for removed in sorted(seen, key=lambda s: (len(s), sorted(s))):
        counts[len(removed)] += 1
        pool = [w for k in range(1,len(removed)+1)
                for subset in combinations(sorted(removed),k)
                for w in groups.get(frozenset(subset), ())]
        found = extension(pool, len(removed)+1)
        if found is not None:
            expanded = [w for i,w in enumerate(code) if i not in removed] + found
            if len(set(expanded)) != 368 or any(close(a,b) for a,b in combinations(expanded,2)):
                raise ValueError('Invalid exchange')
            return counts, expanded
    return counts, None


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--removed',type=int, choices=(1,2,3,4,5),default=4)
    result, witness = search(parser.parse_args().removed)
    print('Connected deletion sets tested by size:', result[1:])
    if witness:
        print('Verified 368-word witness:', ' '.join(''.join(map(str,w)) for w in witness))
    else:
        print('No improving exchange in the tested neighborhood.')
