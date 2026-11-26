"""Search all ten coordinate pairs and every three-symbol projection.

Keep each old word's three projected symbols. For a proposed new projection,
allow both other symbols of nearby old words to change simultaneously.
Reports UNSAT separately from solver conflict-budget cutoffs.
"""
from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations, product
from multiprocessing import Pool

from pysat.solvers import Solver

from check_projection import close, DIGITS, HERE

PAIRS = list(product(DIGITS, repeat=2))
TRIPLES = list(product(DIGITS, repeat=3))
PAIR_CONFLICTS = {p: [q for q in PAIRS if close(p, q)] for p in PAIRS}
TRIPLE_NEIGHBORS = {p: [q for q in TRIPLES if close(p, q)] for p in TRIPLES}


def search_target(code, axes, target, radius, conflict_budget):
    other_axes = tuple(j for j in range(5) if j not in axes)
    prefixes = [tuple(w[j] for j in other_axes) for w in code] + [target]
    old_labels = [tuple(w[j] for j in axes) for w in code]
    at_prefix = defaultdict(list)
    for i, prefix in enumerate(prefixes):
        at_prefix[prefix].append(i)

    cells = set(TRIPLE_NEIGHBORS[target])
    if radius == 2:
        cells = {q for p in cells for q in TRIPLE_NEIGHBORS[p]}
    movable = {i for p in cells for i in at_prefix[p]}
    variable = {}
    clauses = []
    next_id = 1
    for i in sorted(movable):
        forbidden = {q for p in TRIPLE_NEIGHBORS[prefixes[i]]
                     for j in at_prefix[p] if j not in movable
                     for q in PAIR_CONFLICTS[old_labels[j]]}
        labels = [p for p in PAIRS if p not in forbidden]
        if not labels:
            return False, None
        variable[i] = dict(zip(labels, range(next_id, next_id + len(labels))))
        next_id += len(labels)
        clauses.append(list(variable[i].values()))

    for i in sorted(movable):
        for prefix in TRIPLE_NEIGHBORS[prefixes[i]]:
            for j in at_prefix[prefix]:
                if j >= i or j not in movable:
                    continue
                for label, left in variable[i].items():
                    for q in PAIR_CONFLICTS[label]:
                        if q in variable[j]:
                            clauses.append([-left, -variable[j][q]])

    with Solver(name="cadical195", bootstrap_with=clauses) as solver:
        solver.set_phases([variable[i][old_labels[i]] for i in sorted(movable) if i < len(code)])
        solver.conf_budget(conflict_budget)
        result = solver.solve_limited()
        if result is not True:
            return result, None
        true_variables = set(solver.get_model())

    witness = []
    for i, prefix in enumerate(prefixes):
        if i in movable:
            label = next(q for q, v in variable[i].items() if v in true_variables)
        else:
            label = old_labels[i]
        word = [0] * 5
        for j, symbol in zip(other_axes, prefix):
            word[j] = symbol
        for j, symbol in zip(axes, label):
            word[j] = symbol
        witness.append(tuple(word))
    if len(witness) != 368 or any(close(x, y) for x, y in combinations(witness, 2)):
        raise ValueError("SAT model failed the independent full-word check")
    return True, witness


def search_axes(task):
    axes, code, radius_two_budget = task
    for radius, budget in [(1, 1200), (2, radius_two_budget)]:
        counts = {False: 0, None: 0}
        for target in TRIPLES:
            result, witness = search_target(code, axes, target, radius, budget)
            if result is True:
                return witness
            counts[result] += 1
        print(f"axes {axes}, radius {radius}: {counts[False]} UNSAT, "
              f"{counts[None]} budget cutoffs", flush=True)
    return None


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--axes", nargs=2, type=int, choices=range(1, 6),
                        metavar=("FIRST", "SECOND"), help="one pair of coordinates, numbered 1 to 5")
    parser.add_argument("--radius-two-budget", type=int, default=300,
                        help="CaDiCaL conflict budget per radius-two projection")
    args = parser.parse_args()
    if args.radius_two_budget <= 0 or args.workers <= 0:
        parser.error("the conflict budget and worker count must be positive")
    if args.axes and args.axes[0] == args.axes[1]:
        parser.error("the two coordinates must be distinct")
    pairs = ([tuple(i - 1 for i in sorted(args.axes))] if args.axes
             else combinations(range(5), 2))
    seed = [tuple(map(int, w)) for w in (HERE / "polak_schrijver.txt").read_text().split()]
    with Pool(args.workers) as pool:
        tasks = [(axes, seed, args.radius_two_budget) for axes in pairs]
        for witness in pool.imap_unordered(search_axes, tasks):
            if witness is not None:
                print("\n".join("".join(map(str, word)) for word in witness))
                break
