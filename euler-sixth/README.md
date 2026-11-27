# Five sixth powers with repeated summands

Can five positive sixth powers sum to a sixth power? Lander, Parkin and Selfridge discussed the question in 1967. The Equal Sums of Powers archive listed the one-versus-five case as open in October 2026. One exact positive solution would settle existence. Euler’s original conjecture across all exponents was already refuted in 1966 by the identity `27^5 + 84^5 + 110^5 + 133^5 = 144^5`. The pinned Lean project also checks that historical identity. [1966 paper](https://www.ams.org/bull/1966-72-06/S0002-9904-1966-11654-3/S0002-9904-1966-11654-3.pdf) · [1967 survey](https://doi.org/10.1090/S0025-5718-1967-0222008-0) · [Current archive](https://powersums.jorisperrenet.com/)

We searched the family

$$
a^6+2b^6+2c^6=z^6,\qquad a,b,c,z\in\mathbb Z_{>0}.
$$

It permits equal values among the three bases and counts each summand with its multiplicity. No priority or search record is claimed for this restricted family.

## Why the repeated pairs matter

Modulo 8, 9 and 7, a sixth power is either 0 or 1. It is 0 exactly when its base is divisible by 2, 3 and 7, respectively. The five residues sum to at most 5, so they cannot wrap around any of these moduli. A repeated base contributing 1 would contribute it twice. Therefore both `b` and `c` are divisible by 42. For each of 2, 3 and 7, that prime divides `a` exactly when it divides `z`. Dividing all four bases by such a common prime preserves the equation and decreases `z`.

This residue method already appears in the 1967 survey and in Resta and Meyrignac’s later search. The latter paper reports a search below 730,000 for the related equation with six summands. Our certificates concern five summands with two repeated pairs. [Lander, Parkin and Selfridge, pp. 454–455](https://doi.org/10.1090/S0025-5718-1967-0222008-0) · [Resta and Meyrignac, §§2 and 4](https://doi.org/10.1090/S0025-5718-02-01445-X)

There is a complete obstruction when the single summand equals one of the repeated summands. The equation becomes `3u^6 + 2v^6 = z^6`. Modulo 8, an odd `u` would contribute 3 and an odd `v` would contribute 2, while `z^6` can only contribute 0 or 1. Thus all three bases must be even. Halving them gives another solution with a smaller positive `u`, contradicting the existence of a smallest such solution. Lean proves impossibility for every positive `u`, even allowing `v = 0`. [Descent theorem](../lean-qutrit/Euler.lean)

Write `b = 42u`, `c = 42v` and `M = 2 × 42^6 = 10,978,063,488`. It is sufficient to search `z` coprime to 42. Then `a` is also coprime to `M`, and `a^6` and `z^6` have the same remainder modulo `M`. Consequently `a` is congruent to `rz` for one of the 144 sixth roots of unity modulo `M`. The Chinese remainder theorem gives those roots from the 4 roots modulo 128, the 6 modulo 729 and the 6 modulo 117,649. An eligible pair leaves the exact question whether `(z^6-a^6)/M` is the sum of two positive sixth powers. [Lean divisibility theorem](../lean-qutrit/Euler/Sieve.lean) · [Search implementation](search.py)

## Verification

The Lean proof uses a different finite enumeration from the larger search. It lifts the six roots of unity modulo `7^6` one digit at a time. When `a < z < 7^6`, the residue of `a` is its actual value. For `z` coprime to 42 there are only 17 pairs in this range satisfying `a^6 ≡ z^6 mod M`. The corresponding quotient fails the two-sixth-power residue test modulo 8, 9 or 31 in every case. Descent covers the remaining `z`. [Root lifting](../lean-qutrit/Euler/Roots.lean) · [Finite checks](../lean-qutrit/Euler/Check.lean) · [Final theorem](../lean-qutrit/Euler.lean)

Lean 4.24.0 checks the divisibility theorem, the lower bound `117649 ≤ z` and the impossibility of the three-and-two case. These theorems use only `propext`, `Classical.choice` and `Quot.sound`, as reported by `#print axioms`. The historical fifth-power identity uses only `propext`.

The separate exhaustive Python search completed on 27 November 2026 through **`z ≤ 100,000,000`**. It enumerated 17,144,501 eligible pairs `(z,a)`, of which 9,703 passed the first modular filters. None gave a sum of two positive sixth powers for the remaining quotient. The independent floor-sum count agreed exactly. This computational bound applies to the two-repeated-pairs family, including solutions with common factors by descent.

For the larger run, each root gives the integer lattice `a ≡ rz mod M`. The generator changes to a shorter basis using integer operations that preserve the lattice, then enumerates its points inside `1 ≤ a < z ≤ B`. Residue tests remove impossible quotients. For each remaining quotient, the Chinese remainder theorem combines the allowable residues of the smaller base `u` for several coprime moduli. The final loop checks every positive `u` in those classes with `2u^6 ≤ (z^6−a^6)/M` and looks up the complementary sixth power exactly. All arithmetic uses Python integers. A separate floor-sum calculation counts the eligible pairs over the full range. Through one million, direct modular exponentiation recovered the same 1,404 pairs individually, and a separate two-pointer search checked every pair without the modular filters. Known positive sums also test the complementary-power lookup, including equal summands. [Coverage check](check_coverage.py)

From the repository root, run the Python replay and the pinned Lean project with the following commands.

```sh
python3 -B euler-sixth/check_coverage.py 100000000
python3 -B euler-sixth/search.py 100000000
cd lean-qutrit
lake exe cache get $(awk '/^import Mathlib/{print $2}' Qutrit/Basic.lean Qmds/*.lean Shannon/*.lean Euler/*.lean)
lake build
lake env lean Euler.lean
```

## One repeated pair

With one repeated pair, the same residue count forces the repeated base to be divisible by 42. The general five-summand question also permits five distinct bases. The expanded search tests

```text
a^6 + (42u)^6 + (42v)^6 + 2(42w)^6 = z^6
1 ≤ a < z ≤ 500000, u,v,w ≥ 1, gcd(a,42) = gcd(z,42) = 1.
```

Here the singleton carries every exceptional residue at 2, 3 and 7. General five-term solutions could distribute those residues differently. The search groups a and z by sixth power modulo 42⁶ and enumerates w. After modular filters on the remaining sum of two powers, 711 eligible (a,z) pairs give 2,329 complementary tests and zero identities. An independent pass sorts all residues then looks up complementary powers directly. Both passes use exact integers. The extended run through z = 1,000,000 gave 2,806 eligible pairs and 19,699 complementary tests. Both implementations again found no identity. The combined extended search and direct check took 117.2 s on the recorded machine. These bounds are computational results on the displayed family. The earlier Lean statements address different multiplicities.

```sh
python3 -B euler-sixth/search_one_pair.py 500000
python3 -B euler-sixth/check_one_pair.py 500000
python3 -B euler-sixth/search_one_pair.py 1000000
python3 -B euler-sixth/check_one_pair.py 1000000
```

## Erdős problems with finite witnesses

Erdős and Szekeres conjectured in 1935 that any set of `2^(n−2)+1` points in the plane with no three collinear contains `n` points in convex position. Seven vertices is the first open case. A list of 33 points with no three collinear and no seven in convex position would disprove the conjecture. For integer coordinates, all the checks can use exact determinant signs. The classical construction reaches 32 points. A December 2025 study excludes several restricted classes of 33-point candidates, and a November 2026 preprint improves the asymptotic upper bound. The seventh case remains a separate search target. [Erdős Problem 107](https://www.erdosproblems.com/107) · [33-point case study](https://arxiv.org/abs/2512.24061) · [November 2026 upper bound](https://arxiv.org/abs/2611.29344)

Schroeder’s September 2026 preprint reports `33 ≤ ES(7) ≤ 81`. Damásdi, Dong, Scheucher and Zeng prove that adding any point in general position to the classical 32-point construction produces a convex heptagon. A search starting from that construction must therefore change at least one of the original points. [Reported 81-point bound](https://doi.org/10.5281/zenodo.22842891) · [Saturation theorem](https://www.sciencedirect.com/science/article/pii/S0195669825001258)

Erdős and Selfridge asked whether finitely many congruence classes with distinct odd moduli greater than one can cover every integer. A proposed list can be checked over one period, the least common multiple of its moduli. A covering would confirm Erdős’s expectation and disprove Selfridge’s. A July 2026 preprint reports a kernel-checked exclusion of all periods through 10,000. The catalogue lists the full question as open. [Erdős Problem 7](https://www.erdosproblems.com/7) · [Mian and Siddique](https://arxiv.org/abs/2607.25628)
