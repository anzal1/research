"""Check one-coordinate extensions of the 367-word Polak–Schrijver code.

No SAT solver is used in the replay. Each residual obstruction consists of
indices in the published word list, followed by the proposed new word.
"""
from collections import Counter, deque
from itertools import combinations, product
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
DIGITS = range(7)


def close(left, right):
    return all((x - y) % 7 in (0, 1, 6) for x, y in zip(left, right))


def boxes(point):
    for shift in product((0, 1), repeat=len(point)):
        yield tuple((x - step) % 7 for x, step in zip(point, shift))


def can_label(points):
    """Test whether the conflict graph admits a labeling by seven cycle symbols."""
    neighbors = [[] for _ in points]
    for i, j in combinations(range(len(points)), 2):
        if close(points[i], points[j]):
            neighbors[i].append(j)
            neighbors[j].append(i)

    # support[mask] is the set of colors compatible with at least one in mask.
    support = []
    for mask in range(128):
        support.append(sum(1 << b for b in DIGITS if any(
            mask & (1 << a) and (a - b) % 7 in (2, 3, 4, 5) for a in DIGITS)))
    counts = [bin(m).count("1") for m in range(128)]

    def search(domains, changed):
        queue = deque(changed)
        while queue:
            i = queue.popleft()
            for j in neighbors[i]:
                mask = domains[j] & support[domains[i]]
                if not mask:
                    return False
                if mask != domains[j]:
                    domains[j] = mask
                    queue.append(j)
        remaining = [i for i, m in enumerate(domains) if counts[m] > 1]
        if not remaining:
            return True
        i = min(remaining, key=lambda i: (counts[domains[i]], -len(neighbors[i])))
        for color in DIGITS:
            if domains[i] & (1 << color):
                child = domains.copy()
                child[i] = 1 << color
                if search(child, [i]):
                    return True
        return False

    # Rotating all labels lets us prescribe color zero for the additional word.
    return search([127] * (len(points) - 1) + [1], [len(points) - 1])


def main():
    code = [tuple(map(int, w)) for w in (HERE / "polak_schrijver.txt").read_text().split()]
    assert len(code) == len(set(code)) == 367
    assert all(len(w) == 5 and all(x in DIGITS for x in w) for w in code)
    assert all(not close(x, y) for x, y in combinations(code, 2))
    packed = sum(int("".join(map(str, w)), 7) << (15 * i) for i, w in enumerate(code))
    source = (HERE.parent / "lean-qutrit" / "Shannon" / "Boxes.lean").read_text()
    literal = re.search(r"^def appendix : Nat := (0x[0-9a-f]+)$", source, re.MULTILINE)
    assert literal and int(literal.group(1), 16) == packed, "Lean appendix differs from word list"
    cores = {}
    for line in (HERE / "projection_cores.txt").read_text().splitlines():
        axis, prefix, *indices = line.split()
        key = int(axis), tuple(map(int, prefix))
        ids = list(map(int, indices))
        assert key not in cores and len(ids) == len(set(ids))
        assert all(0 <= i < len(code) for i in ids)
        cores[key] = ids

    used = set()
    for axis in range(5):
        projected = [w[:axis] + w[axis + 1:] for w in code]
        loads = Counter(box for p in projected for box in boxes(p))
        assert max(loads.values()) == 3
        saturated = 0
        for p in product(DIGITS, repeat=4):
            if any(loads[box] == 3 for box in boxes(p)):
                saturated += 1
                continue
            key = axis, p
            reduced = [projected[i] for i in cores[key]] + [p]
            if can_label(reduced):
                raise ValueError(f"Colorable obstruction at {key}")
            used.add(key)
        print(f"coordinate {axis + 1}: {saturated} box exclusions, "
              f"{7**4 - saturated} graph exclusions", flush=True)
    assert used == set(cores)


if __name__ == "__main__":
    main()
