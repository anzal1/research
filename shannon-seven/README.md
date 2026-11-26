# Searching for 368 words on the seven-cycle

A word is a five-tuple of residues modulo seven. Two words can be confused when every coordinate differs by 0, 1 or −1 modulo seven. A 368-word code requires all 67,528 unordered pairs to avoid confusion. The published Polak–Schrijver code has 367 words. The searches recorded here have produced no 368-word witness. [Published construction, appendix](https://arxiv.org/pdf/1808.07438)

## Reassigning one coordinate

Choose any one of the five coordinates. Retain the four other symbols of every published word, counting repeated projections with their multiplicities. Append any additional four-symbol projection. Can the missing symbol now be assigned to **each of the 368 words** so that all are distinguishable?

The independent, exact Python check rules this out. There are five choices of the omitted coordinate and 2,401 choices of the additional projection. In 11,983 of these 12,005 cases, a product of four adjacent-symbol pairs already contains three old projections and the proposed fourth. All four missing symbols would have to be pairwise nonadjacent and distinct on the seven-cycle, which has independence number three.

In the other 22 cases, take the indicated subset of published projections and the additional projection. Join two vertices whenever their projections are confusable. A valid assignment must give the endpoints of every edge cyclic distance at least two. The checker rotates the last symbol to zero, removes unsupported symbol choices and branches over all surviving choices whenever propagation stalls. Every branch ends in a conflict. [Independent checker](check_projection.py) · [Obstruction indices](projection_cores.txt)

| Coordinate omitted, counted from the left | Excluded by four points in one box | Remaining graph obstructions |
|---|---:|---:|
| 1 | 2,396 | 5 |
| 2 | 2,398 | 3 |
| 3 | 2,396 | 5 |
| 4 | 2,398 | 3 |
| 5 | 2,395 | 6 |

[The word list](polak_schrijver.txt) preserves the authors’ appendix order and leading zeros. Each row of [projection_cores.txt](projection_cores.txt) specifies the zero-based coordinate, the four-symbol added projection and the zero-based indices of the retained words needed for the contradiction. Run the independent check from the repository root with `python3 -B shannon-seven/check_projection.py`.

## Replaying the proof in Lean

The theorem quantifies over all five omitted coordinates, all 2,401 extra projections and every assignment of 368 missing letters. The `Packing` predicate keeps the 367 rows in appendix order. Two rows with the same shadow still impose a separation constraint. The independent Python replay also checks that Lean’s packed integer decodes to the same 367 words as the text file. [Statement](../lean-qutrit/Shannon/Projection.lean) · [Geometry](../lean-qutrit/Shannon/Geometry.lean)

Lean checks a triple of old rows for each box exclusion. For each remaining graph, a Boolean variable states that a vertex carries a given letter. Each vertex must have a letter, neighboring vertices cannot have confusable letters, and rotating all the labels fixes the last vertex at zero. Mathlib reconstructs a Lean proof of the empty clause from the stored LRAT trace. The kernel compares its input formula with the independently defined coloring constraints. [Box certificates](../lean-qutrit/Shannon/Boxes.lean) · [Encoding and soundness proof](../lean-qutrit/Shannon/Refutation.lean) · [Residual certificates](../lean-qutrit/Shannon/Cores/)

From the repository root, use the pinned Lean toolchain and mathlib revision. The loop builds one residual certificate at a time.

```sh
cd lean-qutrit
lake exe cache get $(awk '/^import Mathlib/{print $2}' Qutrit/Basic.lean Qmds/*.lean Shannon/*.lean)
for file in Shannon/Cores/*.lean; do
  name=$(basename "$file" .lean)
  lake build "Shannon.Cores.$name" || exit 1
done
lake build
lake env lean Shannon.lean
python3 -B ../shannon-seven/check_projection.py
```

Each residual module contains its DIMACS formula and proof trace. To regenerate them, run `lake env python3 -B ../shannon-seven/generate_residual_proofs.py` from `lean-qutrit` with the pinned toolchain’s `cadical` executable on PATH. The independent Python replay needs only the standard library.

Lean 4.24.0 built `Shannon.Seven.no_single_coordinate_extension`. Its `#print axioms` output lists exactly `propext`, `Classical.choice` and `Quot.sound`. The unrestricted existence of a 368-word code remains unresolved by this result.

## Letting two coordinates change

The constructive SAT search retains three coordinates of every old word. It appends a new projection, and frees both remaining coordinates for each old word whose projection is within cyclic distance r of that target in each of the three retained coordinates. Every candidate model goes through a separate direct check of the full five-symbol words. [Search](search_two_coordinates.py)

With radius one, the solver returned UNSAT for all 3,430 combinations of coordinate pair and target projection. With radius two, it returned UNSAT for 1,849 and reached its conflict limit for 1,581. These are solver observations. The cutoffs leave the corresponding instances undecided. The broader 368-word question permits all five coordinates to change.

The initial radius-two run stopped on 14 projections for coordinates three and four and on 18 projections for coordinates four and five. At a budget of 20,000 conflicts, CaDiCaL returned UNSAT on all 343 projections for each pair. Across the ten coordinate pairs, this brings the total to 1,881 radius-two solver exclusions and leaves 1,549 instances undecided. The Lean theorem above covers the one-coordinate problem.

Reproduce the follow-ups with `python -B shannon-seven/search_two_coordinates.py --axes 3 4 --radius-two-budget 20000 --workers 1`, then repeat with `--axes 4 5`. A next search can free coordinates one and two, where 21 projections reached the original limit.

To repeat the constructive search, install `python-sat==1.9.dev25` in a Python environment and run `python -B shannon-seven/search_two_coordinates.py --workers 1` from the repository root. The search tries 1,200 conflicts per radius-one instance and 300 per radius-two instance. CaDiCaL’s model order and implementation can affect the cutoff counts.
