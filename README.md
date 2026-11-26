# Research

Findings from small open problems, each with the code to check it yourself.
Every result here was verified independently before it was published, and each folder says exactly what is claimed and what is not.

| Finding | Result | Status | Check |
|---|---|---|---|
| [King's graph entropy, OEIS A247413](kings-entropy-a247413/) | 26 digits of the constant (OEIS had 18) | In OEIS editor review | `compute_a247413.c`, a few minutes |
| [Qutrit entanglement-assisted codes](qutrit-eaqecc/) | 50 better entries in Grassl's qutrit table | `[[14,3,8;5]]_3` approved in [V3R1T4S #331](https://github.com/elder-plinius/V3R1T4S/pull/331); all 50 sent to Grassl | `check_seeds.py`, `check_degenerate.py`, seconds |

## Lean research

[Two logical qutrits at length 12](lean-qutrit/) gives a reproducible candidate survey, an explicit ternary additive stabilizer and a Lean proof of its optimal distance at six shared pairs.

## Negative results

| Search | Result |
|---|---|
| Same code search over GF(4) against the qubit table ([eaqecc-search](https://github.com/anzal1/eaqecc-search)) | Nothing. 202 codes found, none beat a listed bound. The qubit table is the most studied one, so this was the expected outcome. |

CI in this repo re-runs every check on each push.

Code is MIT licensed. Anzal Abidi.
