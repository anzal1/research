# A second family of full-length Hermitian codes

Let q = 2ʰ with h congruent to 14, 42, 98 or 126 modulo 140. Over GF(q²) there is a Hermitian self-orthogonal extended generalized Reed–Solomon code on all q²+1 projective points, of dimension q−1. Any q−1 coordinates determine the message. All these exponents fall outside the earlier order-25 construction because none is divisible by five. Together the constructions cover 48 of the 350 even residues in each block of 700 exponents. The first example has q = 16,384, length 268,435,457 and dimension 16,383. [Theorem](Order29.lean) · [Encoder and information sets](FullLength.lean) · [Earlier family](README.md)

By the standard Hermitian stabilizer construction this implies a quantum MDS code with parameters [[q²+1, q²−2q+3, q]] over a q-level alphabet. At the first size, this means a mathematical encoding that tolerates any 16,383 erasures at known positions, the optimum at that length and rate. The Lean theorem formalizes the classical encoder, its recovery property and Hermitian orthogonality. The quantum interpretation uses the published stabilizer theorem. [Ball and Vilar, Theorem 1.1](https://arxiv.org/abs/2106.10180) · [Grassl, Beth and Pellizzari on flagged erasures](https://doi.org/10.1103/PhysRevA.56.33)

## Why scale 208 works

Write d = (q+1)/5. Choose w of multiplicative order 29, let t = w+wᵠ and take λ = t⁷+t⁶+t⁴. Binary 11010000 encodes those three coefficients, giving the number 208. Set e = λw. The Ball–Vilar condition reduces to proving that the following expression never vanishes for x in GF(q²).

```text
H(x) = 1 + x^(q+1) + e x^d + (e x^d)^q
```

At zero the value is one. For a nonzero x, write x = uy with y in GF(q) and u of norm one. In characteristic two y is the unique square root of the norm of x. Put z = yᵈ and a = wuᵈ. Then z⁵ = x^(q+1), a⁵ = w⁵, and aᵠ = a⁻¹. There are only five possible angular factors uᵈ. The Dickson identity D₅(A+A⁻¹) = A⁵+A⁻⁵ for D₅(S) = S⁵+S³+S implies D₅(a+aᵠ) = D₅(t). A zero of H would satisfy (λz)(a+aᵠ) = 1+z⁵. Clear the denominator by putting M = 1+Z⁵ and L = λZ. Such a z must be a root of the degree-25 polynomial

```text
F(Z) = M^5 + M^3 L^2 + M L^4 + D₅(t) L^5.
```

The trace satisfies t¹⁴+t¹³+t¹²+t⁹+t⁸+t+1 = 0. The search tries nonzero scalings in this coefficient basis until F has no roots in GF(2¹⁴). Scale 208 is the first. It also gives two identities that transport the result to larger fields.

- Seventy successive modular squarings show Z^(2⁷⁰) = Z modulo F. Every root of F is fixed by the 70th power of the characteristic-two Frobenius map.
- A Bézout identity for F and Z^(2¹⁴)+Z gives 1. No root of F is fixed by the 14th power of Frobenius.

A candidate z in GF(2ʰ) is fixed by the hth power of Frobenius. If it also had period dividing 70 it would be fixed at gcd(h,70) = 14, which contradicts the second certificate. The four exponent classes ensure this gcd and 145 ∣ q+1. This supplies the angular order and integer d throughout the family. [Generated certificate](Order29Data.lean) · [Certificate soundness](RayCertificate.lean) · [Search](search_rays.py)

## Independent first-case check

The second program works directly in GF(2²⁸) using the 29th cyclotomic polynomial. It constructs the order-29 element, the five angular values, and a generator of GF(2¹⁴)ˣ. For every nonzero radius it compares z⁴+z⁻¹ with the five scaled traces. All 16,383 radii pass. Replacing λ by one produces nine failing radii, providing a positive control for the root detector. For every setting 1 through 207 the checker also recovers an actual x and evaluates H(x) = 0 directly. The check covers all inputs by the proved norm decomposition. It does not loop over 268,435,456 inputs separately. [Independent checker](check_order29.py)

## Historical status checked November 27, 2026

Grassl and Rötteler reported full-length, distance-q examples for powers q = 2ʰ with h = 3 through 7 in 2015. In §V.B they suggested q = 4 might be their only exception. Ball and Vilar posed the remaining even-exponent cases in §VII of their 2021 preprint. Vilar still listed them on p. 106 of his 2025 thesis. Both include h = 14. The 2013 Jin–Xing preprint originally appeared to include d = q. Its corrected 2020 version explicitly treats d ≤ q−1 or d = q+1. [Grassl–Rötteler, §V.B](https://arxiv.org/pdf/1502.05267#page=4) · [Ball–Vilar](https://web.mat.upc.edu/simeon.michael.ball/hermitianorthogonalrsIEEE.pdf) · [Vilar, p. 106](https://tesisenred.net/bitstream/handle/10803/694186/TRVA1de1.pdf?isAllowed=y&sequence=1#page=107) · [Corrected Jin–Xing](https://arxiv.org/abs/1311.3009v3)

We searched the exact full-length, dimension and distance parameters, q = 16,384, the even-exponent family, and order-29 constructions, in addition to the existing forward-citation review. Wu’s January 2026 EGRS construction assumes an odd prime-power alphabet in §2. The November 2026 Liu et al. preprint uses the Euclidean inner product in §2.1. Theorem 25 of the November qLRC paper gives a near-MDS construction at this length. Its proof explicitly excludes dimension q−1 from the ordinary GRS construction it invokes. The 2025 Wan–Zhu publisher preview discusses distance q and does not expose the complete parameter ranges. The literature examined yielded no matching earlier construction. Priority and external mathematical review remain outstanding. [Review log](../STATUS.md) · [Wu, §2](https://doi.org/10.12677/aam.2026.151014) · [Liu et al., §2.1](https://arxiv.org/html/2611.30048v1#S2.SS1) · [qLRCs, Theorem 25](https://arxiv.org/html/2611.05335v1) · [Wan–Zhu](https://doi.org/10.1007/s11128-025-04907-2)

## Reproduction and next mathematical question

From the repository root, run `python3 -B harness/run.py all --problem quantum`. To audit the complete Lean project, run `lake build` followed by `lake env lean Qmds.lean` in `lean-qutrit/`. The complete project built successfully on November 27, 2026. Both final declarations, `Qmds.Order29.full_length_family` and `Qmds.Order29.full_length_16384`, printed exactly `[propext, Classical.choice, Quot.sound]`. The build checks the polynomial identities inside the kernel using `decide +kernel`.

The next smaller missing exponent is h = 8, q = 256. Here q+1 = 257 is prime, so the five-direction reduction used above cannot apply. A tractable next experiment is to test g(x) = axᵏ+bx²ᵏ with 1 ≤ k ≤ 127. The existing q = 256 search exhausts a different second exponent, 255. [Exact earlier search scope](README.md)
