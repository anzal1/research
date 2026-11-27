# My dot joined the theorem party

## Opening post

Page 106 of Ricard Vilar’s PhD thesis leaves a quantum coding question open.

For one case, my dot found the coefficient 0xc2073.

One zero would kill the construction. We checked all 1,048,576 inputs. Zero roots.

Lean checked the recipe for infinitely many sizes.

## Reply 1

Those five hex digits are a setting for the encoder. Ball and Vilar needed a formula that never hits zero. At q = 1,024, ours passes that test everywhere. The attached card gives the exact formula so you can try to break it yourself. https://arxiv.org/abs/2106.10180

## Reply 2

What do you get? A design for sending quantum information across 1,048,577 carriers. Any 1,023 can go missing and the message survives if the receiver knows which ones vanished. For the amount of information it carries, that’s the best guarantee physics allows.

## Reply 3

Lean checked the classical code used to build the quantum one. The theorem covers q = 2^h for h = 10, 30, 70 or 90 modulo 100. Other even exponents remain open in the literature we checked. If you know an earlier construction with these parameters, I’d like to read it.

## Image alt text

**Proof card for the opening post.** Vilar's 2025 thesis lists an open existence question. For the q = 1,024 case, the coefficient is 0xc2073 in the specified binary field basis. The card gives the polynomial, the field and the exhaustive check: 1,048,576 inputs, zero roots. Lean verifies the code construction for four infinite classes of exponents.

**Optional introductory diagrams.** The eraser puzzle shows how two dots determine a straight line. The quantum-message illustration shows flagged gaps at known locations.

## Evidence for the author

For the opening, use the coefficient image. The literal integer encodes a field element in the basis given on the card. The infinite theorem chooses an order-25 element at each size. The five digits identify the concrete first example only. The proof and checker are in the local research branch. The linked Ball–Vilar paper is the source of the question. [Thesis, p. 106](https://upcommons.upc.edu/server/api/core/bitstreams/3f9b47cc-9a24-4fd3-90a3-dd30e610a94c/content#page=107) · [Construction](../README.md) · [First-case checker](../check_order25.py)

The straight line is a toy example. In the classical code, the message is a list of 1,023 coefficients. Each numbered clue is a scaled value of its polynomial, except for one special clue that gives the top coefficient. The receiver knows the clue numbers and scales. Any 1,023 intact clues uniquely determine the coefficient list. [Encoder and recovery theorem](../FullLength.lean)

A perfect spare copy of an arbitrary unknown quantum state is impossible. The quantum code distributes the information across many systems. It is a mathematical design for handling flagged losses. [Original no-cloning paper](https://doi.org/10.1038/299802a0)

Lean proves the classical encoder’s recovery guarantee and Hermitian self-orthogonality. The quantum parameters follow from the published Hermitian stabilizer construction. The quantum distance is 1,024. A code of that distance corrects 1,023 erasures at known locations, and this code meets the quantum Singleton bound. [Formal theorem](../FullLength.lean) · [Independent first-case check](../check_order25.py) · [Ball and Vilar, sections II and VII](https://arxiv.org/abs/2106.10180) · [Quantum Singleton bound and erasures](https://arxiv.org/abs/2010.07902)

Vilar listed the remaining even exponents in his 2025 thesis, chapter 7, p. 106. Our search identified no earlier construction covering these exact four classes. Independent confirmation of priority is pending. [Thesis](https://upcommons.upc.edu/server/api/core/bitstreams/3f9b47cc-9a24-4fd3-90a3-dd30e610a94c/content#page=107) · [Dated literature review](../../STATUS.md)
