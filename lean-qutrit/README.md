# Two logical qutrits at length 12

The largest symplectic distance of a ternary additive EA stabilizer with 12 transmitted qutrits, two logical qutrits and six shared maximally entangled pairs is **9**. The lower bound uses cubic polynomials over the ternary field. The upper bound applies to every additive normalizer at these parameters, including degenerate ones.

## What Lean checks

A site is an ordered pair over ℤ/3ℤ. A word has exactly 12 sites. Its weight counts the nonzero pairs and its symplectic product sums their determinants. For a linear subspace N of words, write R = N ∩ N⊥. The parameter predicate requires dim N + c = n + k, dim R + k + c = n, and d to be the **attained** minimum weight in N ∖ R.

These are the normalizer-side equations for a non-catalytic entanglement-assisted stabilizer. Indeed S = N⊥ has dimension 2n − dim N, has the same radical, consumes c = (dim S − dim R)/2 pairs and encodes k = n − dim S + c. The translation from symplectic data to quantum encoders uses the published stabilizer theorem. The Lean objects here are finite vector spaces, their forms and weights. General nonadditive quantum encoders are outside this theorem. At d = 9, Proposition 17 of Baek–Won–Kim also gives c ≥ 6, since σ = 2 and 2(d−1) ≤ n−k+c. This least-entanglement inference uses their published proposition. The new Lean upper bound holds with c fixed at six. [Galindo, Hernando, Matsumoto and Ruano, Theorem 1](https://arxiv.org/abs/1812.05312)

| Declaration | Scope |
|---|---|
| `Qutrit.witness_parameters` | An explicit range of a linear map has parameters (12,2,9,6). |
| `Qutrit.distance_upper` | Every ternary additive normalizer with (n,k,c) = (12,2,6) has d ≤ 9. |
| `Qutrit.optimal_additive_distance` | 9 is the greatest element of the set of attainable distances at those parameters. |

## Candidate selection, 2026-11-27

| Exact question | Evidence before this attempt | Progress criterion |
|---|---|---|
| Does an additive `[[12,2,9;6]]₃` exist? | Grassl lists 8–10 at six pairs and 9–10 at eight pairs. At six pairs, distance ≥10 would have Singleton defect σ = n−k−d+1 < k and would violate Theorem 1 of Baek–Won–Kim. Their Proposition 17 gives c ≥ 6 at d = 9. Their length-eight construction achieves σ = k, and they identify least entanglement at larger lengths as a research question. The reviewed sources leave 8 or 9 at this cell. | Produce a rank-eight normalizer with rank-four radical and prove that every non-radical word has weight ≥9. Alternatively, exclude such a normalizer. |
| Does a binary additive `[[8,2,5;2]]₂` exist? | The qubit table lists 4–5. Proposition 17 permits equality at 5. Its authors exhibit ternary attainment and identify binary attainment as open. | A verified binary normalizer or an exclusion covering all binary additive normalizers at length eight. |
| Can eight shared pairs achieve distance 12 at (n,k) = (13,1) over the ternary field? | Grassl lists 10–12. The repository constructs 11. Baek–Won–Kim already reach 12 in Table 2 of their October preprint, revised November 25. | An independent proof would reproduce a known endpoint. This gap in the database is closed in the literature. |
| For the king's graph, does ⌊10²⁵ κ⌋ equal 13426439511246012978517301, where κ = lim F(n,n)^(1/n²) and F counts independent sets? | OEIS revision 41 lists all 26 digits. Liang and the repository give numerical estimates. Rounding their NAK lower bound down, Chan and Rechnitzer give the interval from 1.342643951124601297851730161875740395719 to 1.342643951124602238. The upper endpoint lies beyond the 26-digit bin. | Certify both endpoints of the 26-digit bin using a rigorous finite-to-infinite bound. Agreement between bond dimensions supplies an estimate. |

The first question needs just four logical coefficients and four radical shifts. Its finite certificate can be recomputed in seconds. The recent papers matter for choosing a cell. For example, at (17,1,11) the table upper bound 16 already drops to 15 for additive codes by Corollary 18. The length-12 target tests an extension of a known construction in the two-logical-qutrit regime. No priority or database acceptance is asserted. [Grassl's qubit table](https://eaqecc.codetables.de/qubit.php) · [Grassl's qutrit table](https://eaqecc.codetables.de/qutrit.php) · [Luo et al.](https://arxiv.org/abs/2207.05647) · [Baek–Won–Kim, Table 2](https://arxiv.org/abs/2610.41183v2) · [Baek–Won–Kim, Theorem 1, Proposition 17 and Section 4](https://arxiv.org/abs/2611.32126v1) · [OEIS A247413 source](https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A247/A247413.seq) · [Liang](https://arxiv.org/abs/2505.12776) · [Chan and Rechnitzer, Tables 1–2](https://arxiv.org/abs/1411.7442)

## Construction

Write p(t) = a + bt + ct² + dt³ as a homogeneous cubic on the projective line. At each of 0, 1, −1 and ∞ use two sites (x,y+h), (x,−h), with an independent shift h. The x value is p at the point. The y value is its first derivative in the local coordinate, multiplied by 1, 1, −1, 1 respectively. At infinity the value and derivative are d and c. This is the rational-point pair construction of Baek–Won–Kim, Appendix B.3. [Length-eight baseline](https://arxiv.org/abs/2611.32126v1)

For the four extra sites, reduce p modulo t²+1 and t²+t+2. Each is irreducible over the ternary field. For each remainder X + Zt append (X,Z) and (X,−Z). Their Gram contributions cancel. Both sites vanish exactly when the quadratic divides p, which uses two degrees. On each rational pair the number of zeros is at most the root multiplicity truncated at two. A nonzero cubic has at most three zeros counted this way, including infinity. Hence every logical word has weight at least nine. The cubic t³−t with zero shifts attains nine.

The eight coefficient directions are independent. The four shifts are in the radical. On (a,b,c,d) the restricted alternating form has upper-triangular entries (1,1,0,0,1,−1) in lexicographic order. Its Pfaffian equals −2, which is nonzero modulo three. The radical is therefore exactly the span of the shifts. Lean derives the radical from the symplectic product and checks a finite inequality over the 80 nonzero cubics. This gives a second route to the polynomial root-count argument.

## Why ten is impossible

Start with any candidate N of dimension eight and its radical R of dimension four. Pick three sites in turn. Whenever the subspace of radical words vanishing on the sites already picked is nonzero, take a site where one such word is nonzero. Each pick lowers the dimension of that subspace by at least one. After three picks at most one radical dimension survives. In the full normalizer at least two dimensions survive, since three pairs impose at most six scalar constraints. Some surviving word is outside the radical and has weight at most nine.

## Independent checks and reproduction

Install elan and Python 3. The toolchain file selects Lean 4.24.0. The Lake manifest locks mathlib and its transitive dependencies. From this directory run

```sh
lake exe cache get $(awk '/^import Mathlib/{print $2}' Qutrit/Basic.lean)
lake build
lake env lean Qutrit.lean
python3 -B check.py
```

The last Lean command prints the axioms of all three final declarations even on a cached build. Each reports precisely `[propext, Classical.choice, Quot.sound]`. CI checks this list for each theorem. The independent Python computation constructs generators by polynomial division, takes the symplectic dual twice by Gaussian elimination, and enumerates the recovered basis. The rank of the stabilizer Gram matrix is 12. The 6,480 non-radical words have the following exact weights.

| Weight | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|
| Count | 1,488 | 1,152 | 1,440 | 2,400 |

## Reusing the workflow

1. Specify the extremum, field, code class and resource model. Record the dated table interval and check recent primary papers, including propagation rules.
2. Choose a finite milestone with a witness or an exclusion criterion. Keep search outside the proof. Here polynomial remainders select the extra sites and independent elimination checks the candidate.
3. State the mathematical predicate before certifying the witness. Include rank, degeneracy, a universal lower bound on weight and an attaining word. Prove a universal upper bound separately if claiming a maximum.
4. Build from the lockfile, inspect the final declarations' axiom dependencies and rerun the independent computation. Record the limits of both checks and the status of the original question.

**Next tractable step.** Test length 14 with the two signed copies associated to the third monic irreducible quadratic, t²−t+2. The candidate parameters are `[[14,2,11;8]]₃`. The extra two sites preserve the Gram form and their simultaneous vanishing uses two degrees of the cubic. A length-14 kernel theorem would extend the result to another cell. Least entanglement for arbitrary lengths and the nonadditive case remain unresolved here.
