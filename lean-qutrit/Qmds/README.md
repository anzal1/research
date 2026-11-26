# Two finite-field questions from quantum MDS coding

## Full length at q = 256

Ball and Vilar identified an outstanding case of a question already studied by Grassl and Rötteler in 2015. Does there exist a length-65,537 Hermitian self-orthogonal generalized Reed–Solomon code of dimension 255 over the field of 65,536 elements? Section VII of Ball–Vilar singles out even exponents h ≥ 8 in q = 2ʰ. Their criterion asks for coefficients of a polynomial g of degree at most 255 and a base-field constant c such that the following function has no zero anywhere in the quadratic extension K of F = GF(256). A constant term of g can be absorbed into c. [Ball–Vilar, Theorem 3.2 and Section VII](https://arxiv.org/abs/2106.10180) · [Grassl–Rötteler, Section V](https://arxiv.org/abs/1502.05267)

```text
H(x) = c + x^257 + g(x) + g(x)^256
```

**Kernel-checked exclusions.** Every monomial g(x) = e xⁱ, 1 ≤ i ≤ 255, has a root of H, for arbitrary e and c. So does every binomial g(x) = a xⁱ + b xʲ with i + j = 257 and 1 ≤ i,j ≤ 255. Both results include zero coefficients. Lean quantifies over every field K of cardinality 65,536 and characteristic two. It expresses membership in the base field by c²⁵⁶ = c. [Proof](TraceObstruction.lean)

For the first result choose x on the norm fiber x²⁵⁷ = c. Write x = yu, where y = c¹²⁸ belongs to F and u²⁵⁷ = 1. When e ≠ 0, take u = e^(255j) with 1 + 255ji divisible by 257. This j exists because 257 is prime and i is between 1 and 255. Then euⁱ is a 257th power, so it belongs to F. Multiplication by yⁱ keeps it there. Its relative trace is zero in characteristic two. The norm cancels c. When i+j=257, conjugation swaps uⁱ and uʲ on the unit circle, allowing the trace of both terms to be combined into a single trace on the same fiber.

**Independent exhaustive search in another family.** The C++ checker tests g(x) = e xᵏ + f x²⁵⁵ for every 1 ≤ k < 255. The normalization is exact. At c = 0 the origin is a root. Otherwise rescale x by a base-field square root of c and divide H by c. Now c = 1. Rotate x by a norm-one element so that the first coefficient is in F, using the monomial argument. Zero first coefficients are covered by the monomial theorem. On the ray x ∈ F*, the first term now has trace zero, x²⁵⁵ = 1, and squaring permutes F*. A root-free candidate must therefore have Tr(f) = 1. This leaves 254 · 255 · 256 = 16,581,120 cases.

The program decomposes each nonzero x uniquely as uy, where u has norm one and y belongs to F*. On this ray the equation becomes y² + A yᵏ = C, with A = e Tr(uᵏ) and C = 1 + Tr(fu²⁵⁵). It computes the image of the left side for every A and k, then finds a ray on which C belongs to that image. **Each of the 16,581,120 candidates has a root.** This enumeration is a computational exclusion. The two Lean exclusions above have independent algebraic proofs. The full degree-255 existence problem remains unresolved by this work. [Search implementation](search.cpp)

## Affine lengths at distance four

Grassl–Rötteler Conjecture 15 asks for distance-four quantum MDS codes of every length from 6 through q²+2 when q is a power of two other than 4. Ball and Vilar revisit this question separately from their full-length, dimension-(q−1) problem. [2015 conjecture](https://arxiv.org/abs/1502.05267) · [2022 discussion](https://arxiv.org/abs/2106.10180)

The Lean theorem `AffinePuncture.all_affine_lengths` constructs the puncture-code moments for **every** 6 ≤ n ≤ q² when q ≥ 11. It gives n distinct affine evaluation points and nonzero base-field weights that annihilate all nine Hermitian Gram entries for the three rows 1, x, x². It works over any extension containing β outside the base field with an endomorphism fixing the base field. Take the extension GF(q²) and the endomorphism x ↦ xᵠ for coding theory. [Lean theorem](AffinePuncture.lean)

The points lie on parallel lines βb + t indexed by b in the base field. Each occupied line holds at least six points. Assign its points the nonzero Lagrange weights w(t) = 1 / ∏(t−u), the product over the other selected points of that line. Interpolation shows that the weighted sum of any polynomial of degree ≤ 4 vanishes. On a fixed line each Gram entry is such a polynomial in t, since conjugation fixes t. The formal length argument partitions n across at most q lines. For the usual coding interpretation, lift the weights along the surjective norm map. The three scaled Vandermonde rows are then Hermitian self-orthogonal, and any three columns are independent. The Hermitian stabilizer construction yields the distance-four code. The Lean declaration checks the distinct-point and weighted-moment construction.

**Prior work matters here.** A published distance bound for length n = mq−ℓ is d ≤ (q+1−⌊ℓ/m⌋)/2 as a *construction range*. For q ≥ 16 and q < n ≤ q², choose m = ⌈n/q⌉ ≥ 2 and 0 ≤ ℓ ≤ q−1. This range already includes d = 4. For 6 ≤ n ≤ q the shorter Reed–Solomon constructions apply. At q = 8 Grassl and Rötteler report all the required weights computationally. The q²+1 endpoint for q ≥ 8 is covered at d = 4 by Jin–Xing, and Grassl–Rötteler Theorem 14 gives the q²+2 endpoint, including q = 2. Consequently the formal affine theorem should be credited as a direct verification of an infinite family. These sources give pre-existing constructions or computations for the parameter ranges of Conjecture 15. [Jin, Ling, Luo and Xing](https://doi.org/10.1109/TIT.2010.2054174) · [Summary, Table 3, class 3](https://dr.ntu.edu.sg/server/api/core/bitstreams/0f4dbe79-3106-4340-b70c-967fb439a035/content) · [Grassl, Beth and Rötteler, Theorem 14](https://arxiv.org/abs/quant-ph/0312164) · [Jin–Xing](https://arxiv.org/abs/1311.3009)

## Reproduction

From `lean-qutrit/` use the existing Lean toolchain and dependency lockfile.

```sh
lake exe cache get $(awk '/^import Mathlib/{print $2}' Qutrit/Basic.lean Qmds/*.lean)
lake build
lake env lean Qmds.lean
c++ -std=c++17 -O3 Qmds/search.cpp -o /tmp/qmds-search
/tmp/qmds-search
```

All three final Lean theorems depend on `[propext, Classical.choice, Quot.sound]`. The expected search output is `16581120 normalized candidates tested; each has a root`. A next tractable experiment is to test the nonreciprocal families whose exponents are k and 2k for 1 ≤ k ≤ 127, retaining a direct full-field evaluation for every proposed root-free witness.
