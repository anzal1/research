# Research

Findings from small open problems, each with the code to check it yourself.
Every result here was verified independently before it was published, and each folder says exactly what is claimed and what is not.

| Finding | Result | Status | Check |
|---|---|---|---|
| [King's graph entropy, OEIS A247413](kings-entropy-a247413/) | 26 digits of the constant (OEIS had 18) | In OEIS editor review | `compute_a247413.c`, a few minutes |
| [Qutrit entanglement-assisted codes](qutrit-eaqecc/) | 50 better entries in Grassl's qutrit table | `[[14,3,8;5]]_3` approved in [V3R1T4S #331](https://github.com/elder-plinius/V3R1T4S/pull/331); all 50 sent to Grassl | `check_seeds.py`, `check_degenerate.py`, seconds |

## Lean research

[Two logical qutrits at length 12](lean-qutrit/) gives a reproducible candidate survey, an explicit ternary additive stabilizer and a Lean proof of its optimal distance at six shared pairs.

[Full-length Reed–Solomon codes](lean-qutrit/Qmds/) gives a Lean-checked solution to an infinite family of even-exponent cases posed by Ball and Vilar, beginning at q = 1024.

[Five-symbol codes on the seven-cycle](shannon-seven/) proves that reassigning one coordinate in every word of the published 367-word code cannot make room for a 368th word. Lean and an independent Python checker cover all 12,005 choices of coordinate and extra projection.

[Five sixth powers with two repeated pairs](euler-sixth/) proves in Lean that three copies of one positive sixth power and two copies of another can never sum to a sixth power. For `a^6 + 2b^6 + 2c^6 = z^6`, the repeated bases must be divisible by 42 and the right-hand base must satisfy `z ≥ 117649`.

## Negative results

| Search | Result |
|---|---|
| Same code search over GF(4) against the qubit table ([eaqecc-search](https://github.com/anzal1/eaqecc-search)) | Nothing. 202 codes found, none beat a listed bound. The qubit table is the most studied one, so this was the expected outcome. |

CI in this repo re-runs every check on each push.

Code is MIT licensed. Anzal Abidi.
