# New qutrit entanglement-assisted quantum codes (50 table cells)

**Result:** 50 entries in Markus Grassl's qutrit EAQECC table ([eaqecc.codetables.de/qutrit.php](https://eaqecc.codetables.de/qutrit.php)) get a better minimum distance than the table listed on 2026-10-17. 34 come from pure codes, 16 from degenerate (impure) codes.

**Status:**
- `[[14,3,8;5]]_3` was independently re-checked by the V3R1T4S maintainer and is in [PR #331](https://github.com/elder-plinius/V3R1T4S/pull/331), approved to merge after a text fix (done).
- All 50 cells were sent to Markus Grassl on 2026-10-17. He is working through a backlog and will check them against earlier submissions.

## How the pure codes work

Each pure cell comes from one of 14 seed codes `D = [n, M, d]_9` over GF(9) with `D` Hermitian self-orthogonal (`H H^dagger = 0`). By Proposition 1 and Theorem 6 of Luo, Ezerman, Grassl and Ling ([arXiv:2207.05647](https://arxiv.org/abs/2207.05647)) such a seed gives qutrit codes along a diagonal of the table, and puncturing or shortening gives more cells. The seeds were found by computer search over quasi-cyclic, quasi-twisted and small Fourier block structures. They are search results, not theorems.

## How the degenerate codes work

For k = 1: take the repetition code `[N, 1, N]_9` and add ell blocks of length 3, each carrying the stabilizer `(1, 1, 1)`. Over GF(3), 1 + 1 + 1 = 0, so each block is self-orthogonal. The result is `[[N + 2 ell, 1, N + ell; N - 1]]_3`. Its pure distance is only 3, so it is genuinely degenerate. All 16 were checked by exhaustive symplectic enumeration. This trick is specific to characteristic 3 and does not work for qubits.

These codes have d > (n + 2)/2, where the entanglement-assisted Singleton bound is known not to hold in general, so no optimality is claimed. Nine of them reach the table's current upper bound.

## Check it yourself

    python3 check_seeds.py seeds.magma      # the 14 seeds, needs numpy, about 5 seconds
    python3 check_degenerate.py             # the 16 degenerate codes, standard library, under a second
    python3 check_eaqecc.py code_14_3_8_5.json

`seeds.magma` is the same check written for Magma. It was not run here; `check_seeds.py` is the tested version. `code_14_3_8_5.json` is the full stabilizer matrix of `[[14,3,8;5]]_3`.

## Pure cells (34)

| Cell (n, k, c) | New code | Table before | Gain | Seed |
|---|---|---|---|---|
| (11, 0, 5) | [[11,0,8;5]]_3 | 7-9 | +1 | [14,6,8]_9 |
| (11, 0, 7) | [[11,0,9;7]]_3 | 8-10 | +1 | [12,3,9]_9 |
| (12, 0, 4) | [[12,0,8;4]]_3 | 7-9 | +1 | [14,6,8]_9 |
| (12, 0, 6) | [[12,0,9;6]]_3 | 8-10 | +1 | [12,3,9]_9 |
| (12, 0, 9) | [[12,0,10;9]]_3 | 9-11 | +1 | [14,3,11]_9 |
| (13, 0, 3) | [[13,0,8;3]]_3 | 7-9 | +1 | [14,6,8]_9 |
| (13, 0, 9) | [[13,0,11;9]]_3 | 10-12 | +1 | [14,3,11]_9 |
| (14, 0, 2) | [[14,0,8;2]]_3 | 7-9 | +1 | [14,6,8]_9 |
| (14, 0, 8) | [[14,0,11;8]]_3 | 9-12 | +2 | [14,3,11]_9 |
| (14, 3, 5) | [[14,3,8;5]]_3 | 7-10 | +1 | [14,6,8]_9 |
| (15, 0, 7) | [[15,0,10;7]]_3 | 9-12 | +1 | [16,5,10]_9 |
| (16, 0, 6) | [[16,0,10;6]]_3 | 9-12 | +1 | [16,5,10]_9 |
| (16, 0, 8) | [[16,0,11;8]]_3 | 10-13 | +1 | [18,6,11]_9 |
| (17, 0, 7) | [[17,0,11;7]]_3 | 10-13 | +1 | [18,6,11]_9 |
| (18, 0, 6) | [[18,0,11;6]]_3 | 10-13 | +1 | [18,6,11]_9 |
| (18, 0, 10) | [[18,0,12;10]]_3 | 11-15 | +1 | [21,7,12]_9 |
| (18, 0, 12) | [[18,0,14;12]]_3 | 13-16 | +1 | [18,3,14]_9 |
| (19, 0, 9) | [[19,0,12;9]]_3 | 11-15 | +1 | [21,7,12]_9 |
| (19, 0, 11) | [[19,0,13;11]]_3 | 12-16 | +1 | [21,6,13]_9 |
| (20, 0, 8) | [[20,0,12;8]]_3 | 11-15 | +1 | [21,7,12]_9 |
| (20, 0, 10) | [[20,0,13;10]]_3 | 12-16 | +1 | [21,6,13]_9 |
| (21, 0, 7) | [[21,0,12;7]]_3 | 11-15 | +1 | [21,7,12]_9 |
| (21, 0, 9) | [[21,0,13;9]]_3 | 12-16 | +1 | [21,6,13]_9 |
| (21, 0, 16) | [[21,0,17;16]]_3 | 16-19 | +1 | [22,3,18]_9 |
| (22, 0, 16) | [[22,0,18;16]]_3 | 17-20 | +1 | [22,3,18]_9 |
| (23, 0, 13) | [[23,0,16;13]]_3 | 13-19 | +3 | [24,6,16]_9 |
| (24, 0, 12) | [[24,0,16;12]]_3 | 13-19 | +3 | [24,6,16]_9 |
| (25, 0, 11) | [[25,0,14;11]]_3 | 13-19 | +1 | [26,8,14]_9 |
| (26, 0, 10) | [[26,0,14;10]]_3 | 13-19 | +1 | [26,8,14]_9 |
| (26, 0, 18) | [[26,0,19;18]]_3 | 14-23 | +5 | [26,4,19]_9 |
| (27, 0, 18) | [[27,0,18;18]]_3 | 15-23 | +3 | [28,5,19]_9 |
| (28, 0, 18) | [[28,0,19;18]]_3 | 16-24 | +3 | [28,5,19]_9 |
| (29, 0, 18) | [[29,0,19;18]]_3 | 17-24 | +2 | [30,6,20]_9 |
| (30, 0, 18) | [[30,0,20;18]]_3 | 18-25 | +2 | [30,6,20]_9 |

## Degenerate cells (16, k = 1)

| Cell (n, k, c) | New code | Table before | ell | Base code | Reaches table upper bound |
|---|---|---|---|---|---|
| (12, 1, 9) | [[12,1,11;9]]_3 | 10-11 | 1 | [10,1,10]_9 | yes |
| (13, 1, 8) | [[13,1,11;8]]_3 | 10-12 | 2 | [9,1,9]_9 | no |
| (13, 1, 10) | [[13,1,12;10]]_3 | 11-12 | 1 | [11,1,11]_9 | yes |
| (14, 1, 9) | [[14,1,12;9]]_3 | 11-13 | 2 | [10,1,10]_9 | no |
| (14, 1, 11) | [[14,1,13;11]]_3 | 12-13 | 1 | [12,1,12]_9 | yes |
| (15, 1, 10) | [[15,1,13;10]]_3 | 12-14 | 2 | [11,1,11]_9 | no |
| (15, 1, 12) | [[15,1,14;12]]_3 | 13-14 | 1 | [13,1,13]_9 | yes |
| (16, 1, 11) | [[16,1,14;11]]_3 | 13-15 | 2 | [12,1,12]_9 | no |
| (16, 1, 13) | [[16,1,15;13]]_3 | 14-15 | 1 | [14,1,14]_9 | yes |
| (17, 1, 12) | [[17,1,15;12]]_3 | 14-16 | 2 | [13,1,13]_9 | no |
| (17, 1, 14) | [[17,1,16;14]]_3 | 15-16 | 1 | [15,1,15]_9 | yes |
| (18, 1, 15) | [[18,1,17;15]]_3 | 16-17 | 1 | [16,1,16]_9 | yes |
| (19, 1, 14) | [[19,1,17;14]]_3 | 15-18 | 2 | [15,1,15]_9 | no |
| (19, 1, 16) | [[19,1,18;16]]_3 | 17-18 | 1 | [17,1,17]_9 | yes |
| (20, 1, 15) | [[20,1,18;15]]_3 | 16-19 | 2 | [16,1,16]_9 | no |
| (20, 1, 17) | [[20,1,19;17]]_3 | 18-19 | 1 | [18,1,18]_9 | yes |
