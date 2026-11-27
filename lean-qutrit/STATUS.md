# Research status checked November 27, 2026

## Full-length Hermitian Reed–Solomon codes

The priority question is whether a prior proof constructs a Hermitian self-orthogonal extended GRS code over GF(q²) with length q²+1 and dimension q−1 for q = 1024, or for the whole family q = 2ʰ with h congruent to 10, 30, 70 or 90 modulo 100. The quantum distance corresponding to this particular classical dimension is d = q.

- **Documented open status.** Ball and Vilar identify even h ≥ 8 in Section VII of their 2021 preprint, published in 2022. Vilar’s 2025 thesis repeats the outstanding cases on p. 106. The case h = 10 falls directly in both statements. [Journal paper](https://web.mat.upc.edu/simeon.michael.ball/hermitianorthogonalrsIEEE.pdf) · [Thesis](https://upcommons.upc.edu/server/api/core/bitstreams/3f9b47cc-9a24-4fd3-90a3-dd30e610a94c/content)
- **A prior claim was corrected.** The 2013 Jin–Xing preprint claimed every d ≤ q+1 at full length. Ball identified the faulty corollary and the q = 4 counterexample in Section 3. Jin and Xing’s July 2020 revision gives d ≤ q−1 or d = q+1. The original abstract alone would give the wrong priority assessment. [Original version](https://arxiv.org/abs/1311.3009v1) · [Ball’s analysis](https://web.mat.upc.edu/simeon.michael.ball/quantummds.pdf) · [Revised version](https://arxiv.org/abs/1311.3009v3)
- **Later literature.** The OpenAlex forward-citation query for the IEEE paper returned 29 records. I screened their titles, inspected relevant papers or abstracts, and also searched for full-length GRS constructions, the exceptional distance d = q and even powers of two. Hu–Ji’s September 2026 construction assumes odd q. Section 2.1 of Liu et al.’s November 23, 2026 preprint specifies the Euclidean inner product. Wan–Zhu’s August 2025 publisher abstract discusses distance q without giving the full-length parameters. I could check only the publisher preview for that paper. [Citation query](https://api.openalex.org/works?filter=cites:W3176234222&per_page=100) · [Hu–Ji](https://arxiv.org/abs/2609.09943) · [November preprint, Section 2.1](https://arxiv.org/html/2611.30048v1#S2.SS1) · [Wan–Zhu](https://link.springer.com/article/10.1007/s11128-025-04907-2)

I found no earlier valid construction for q = 1024 or the four residue classes in the materials checked. This establishes documented open status at the cited dates. Historical priority remains unconfirmed. On the research branch, the pinned Lean build verified the classical family theorem and its MDS information-set property, and the independent program again found zero roots at all 1,048,576 inputs for q = 1024. The full even-exponent question remains open in the literature reviewed. [Theorem and reproduction](Qmds/README.md)

The subsequent [order-29 result and its priority review](Qmds/ORDER29.md) treat q = 16,384 and four disjoint exponent classes modulo 140. The exact first case has an independent finite-field replay.

## An older open problem from Claude Shannon’s zero-error theory

Seven symbols lie on a circle. Two symbols can be confused when they coincide or are neighbors. Let M(m) be the largest number of length-m words such that every pair differs in at least one coordinate by cyclic distance at least two. Determine Θ(C₇) = sup over m ≥ 1 of M(m)^(1/m). Shannon introduced zero-error capacity in 1956. Lovász solved the five-cycle in 1979 and obtained the seven-cycle upper bound 7 cos(π/7)/(1+cos(π/7)) = 3.31766720… . Tandon’s August 2026 preprint reports a lower bound of 3.25883262… and identifies the exact seven-cycle capacity as open. [Shannon](https://doi.org/10.1109/TIT.1956.1056798) · [Lovász](https://doi.org/10.1109/TIT.1979.1055985) · [Tandon](https://arxiv.org/abs/2608.30273)

A September 2026 preprint reports a slightly stronger capacity lower bound, 3.258834362237710794…, from a 560-coordinate construction. The 368-word five-coordinate target would improve both reported bounds. [September research record](https://aixiv.online/abs/2609.03058)

**Verified baseline.** I read the 367 five-symbol words from the appendix of Polak and Schrijver’s paper and checked all 67,161 unordered pairs. Zero pairs were confusable. The closed neighborhoods of these words cover all 7⁵ = 16,807 possible words, so this particular code cannot be enlarged by appending one word. Whether a different five-symbol code has 368 words is a finite research target. Such a witness would give Θ(C₇) ≥ 368^(1/5) = 3.25963943…, above the 2026 lower bound. [Polak and Schrijver, appendix](https://arxiv.org/pdf/1808.07438)

To reproduce the pair and neighborhood counts, convert the authors’ PDF with Poppler’s `pdftotext -layout` and run the following from the same directory.

```sh
curl -fsSL https://arxiv.org/pdf/1808.07438 -o c7.pdf
pdftotext -layout c7.pdf c7.txt
python3 - <<'PY'
from itertools import combinations, product
from pathlib import Path
import re

appendix = Path("c7.txt").read_text().split("Appendix: explicit code", 1)[1].split("References", 1)[0]
code = [tuple(map(int, word)) for word in re.findall(r"\b[0-6]{5}\b", appendix)]
assert len(code) == len(set(code)) == 367
pairs = list(combinations(code, 2))
conflicts = sum(all((a-b) % 7 in (0, 1, 6) for a, b in zip(x, y)) for x, y in pairs)
covered = {tuple((a+d) % 7 for a, d in zip(x, delta))
           for x in code for delta in product((-1, 0, 1), repeat=5)}
assert (len(pairs), conflicts, len(covered)) == (67161, 0, 16807)
print(len(code), len(pairs), conflicts, len(covered))
PY
```

## A historical disproof from Euler’s number theory

Euler conjectured that a positive nth power requires at least n smaller positive nth powers to represent it as a sum, for n > 2. Lander and Parkin disproved this in 1966. Direct integer arithmetic verifies 27⁵ + 84⁵ + 110⁵ + 133⁵ = 144⁵ = 61,917,364,224. This is their historical counterexample. [Lander and Parkin’s original paper](https://www.ams.org/bull/1966-72-06/S0002-9904-1966-11654-3/S0002-9904-1966-11654-3.pdf)
