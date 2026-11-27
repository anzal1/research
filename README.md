# Research

Reproducible mathematical results from coding theory, combinatorics and number theory. The research harness runs three short searches from the repository root.

```sh
python3 -B harness/run.py search
```

To regenerate the coding certificate and audit the pinned Lean theorems, use the full replay instructions. [Harness](harness/) · [Recorded outputs and timings](harness/results.json)

## Results

| Problem | Result | Evidence |
|---|---|---|
| Full-length Hermitian Reed–Solomon codes | Two constructions cover eight disjoint classes of even exponents. Their first alphabet sizes are q = 1,024 and q = 16,384. Historical priority awaits independent review. | Lean proofs of the classical encoders and independent first-case checks. [Order 25](lean-qutrit/Qmds/) · [Order 29](lean-qutrit/Qmds/ORDER29.md) |
| Five-symbol codes on the seven-cycle | Reassigning one coordinate of every word in the published 367-word seed cannot accommodate a 368th word. The search for a different 368-word code remains open. | Lean and Python cover all 12,005 choices of coordinate and added projection. The two-coordinate solver results are reported separately. [Proof and searches](shannon-seven/) |
| Five positive sixth powers | Three copies of one sixth power plus two of another cannot equal a sixth power. Bounded searches found no identity through 100,000,000 for two repeated pairs, or through 1,000,000 for the specified one-pair family. | Lean proves the three-and-two obstruction. The larger exclusions use exact integer searches. [Statements and bounds](euler-sixth/) |
| Two logical qutrits at length 12 | The optimal additive distance with six shared pairs is 9. | Explicit stabilizer, matching upper bound in Lean and independent symplectic enumeration. [Proof and checker](lean-qutrit/) |
| Qutrit entanglement-assisted codes | Codes for 50 cells improved on Grassl’s qutrit table as recorded on October 17, 2026. | Checks for 14 pure-code seeds, 16 degenerate codes and an explicit stabilizer. [Codes and submission history](qutrit-eaqecc/) |
| King’s graph entropy, OEIS A247413 | Four transfer-matrix truncations agree on 26 digits of the estimated constant. | Numerical convergence and a separate corner-transfer-matrix comparison. [Calculation and expected output](kings-entropy-a247413/) |

A separate search over GF(4) tested 202 codes against the qubit table and found no improvement. [Search repository](https://github.com/anzal1/eaqecc-search)

The verification workflow runs on pushes to `main` and supports manual runs. [CI checks](.github/workflows/verify.yml) · [MIT license](LICENSE)
