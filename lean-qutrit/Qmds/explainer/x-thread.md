# My dot joined the theorem party

## Opening post

my dot joined the theorem party. ●

I’ll encode a message in 1,048,577 symbols. You pick 1,047,554 to erase.

I can recover the whole classical message from the 1,023 you left. Here’s the quantum coding question hiding in that trick.

## Reply 1

Try it with three numbers. I write 4, 7 and their sum, 11. Cover any one and the other two give it back.

Reed–Solomon codes do this with polynomials. Any 1,023 surviving symbols, together with their positions, pin down the polynomial carrying our message.

## Reply 2

The recovery trick is classic. The hard part was making the code obey an extra symmetry called Hermitian self-orthogonality. It lets you build a quantum error-correcting code.

We found a construction for infinitely many cases Ball and Vilar left open. https://arxiv.org/abs/2106.10180

## Reply 3

The first quantum code stores 1,046,531 quantum symbols in 1,048,577 systems with 1,024 levels each. Lose any 1,023 systems and it can recover the quantum information if you know which ones vanished.

That reaches the theoretical limit for this length and message size.

## Reply 4

Lean checked the classical construction for every q = 2^h with h = 10, 30, 70 or 90 modulo 100. At q = 1,024 we also tested the key polynomial at all 1,048,576 field elements. Zero roots.

Other even exponents remain open in the work we reviewed. Earlier references welcome.

## Image alt text

One construction at 1,048,577 positions gives two different guarantees. Keep any 1,023 symbols of the classical code to recover the original message. In the derived quantum code, lose any 1,023 positions and recover the encoded quantum information when the erased positions are known. The classical construction is Lean-verified for infinitely many cases of Ball and Vilar’s question.

## Evidence for the author

Lean proves the classical encoder’s recovery guarantee and Hermitian self-orthogonality. The quantum parameters follow from the published Hermitian stabilizer construction. The quantum distance is 1,024. A code of that distance corrects 1,023 erasures at known locations, and this code meets the quantum Singleton bound. [Formal theorem](../FullLength.lean) · [Independent first-case check](../check_order25.py) · [Ball and Vilar, sections II and VII](https://arxiv.org/abs/2106.10180) · [Quantum Singleton bound and erasures](https://arxiv.org/abs/2010.07902)

Vilar listed the remaining even exponents in his 2025 thesis, chapter 7, p. 106. Our search identified no earlier construction covering these exact four classes. Independent confirmation of priority is pending. [Thesis](https://upcommons.upc.edu/server/api/core/bitstreams/3f9b47cc-9a24-4fd3-90a3-dd30e610a94c/content#page=107) · [Dated literature review](../../STATUS.md)
