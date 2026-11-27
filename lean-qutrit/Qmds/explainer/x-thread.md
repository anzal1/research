# My dot joined the theorem party

## Opening post

my dot joined the theorem party. you get the eraser. ●

I turn a note into 1,048,577 numbered clues. You wipe out all but 1,023. You pick which ones survive.

Hand me those scraps and I can read the whole note. Want to see how? Erase a dot.

## Reply 1

Three dots on a straight line. The left one is at height 2, the right one at 6. Rub out the dot halfway across. How high was it?

Four. The two dots you kept still fix the whole line. Our note lives in a more complicated curve. Any 1,023 numbered clues pin it down.

## Reply 2

Now imagine trying to send a quantum message. You can photocopy a paper note for safekeeping. Physics won’t let you make a perfect spare copy of an unknown quantum message.

So you spread the information across many carriers. Losing some of them can leave the message intact.

## Reply 3

The missing-dot trick is old. Ball and Vilar asked whether this particular code design could also obey the extra rules of quantum error correction at certain sizes.

We found a recipe for infinitely many sizes they left open. Lean, a program that checks math proofs, verified it.

## Reply 4

Picture a receiver that knows which signals never arrived. With our first quantum code, any 1,023 of its 1,048,577 signals can vanish and the receiver can still recover the message.

That’s the most losses a code of this size can guarantee while carrying this much information.

## Image alt text

**Opening image.** Three evenly spaced pencil marks lie on a straight line. The left mark is at height 2 and the right mark is at 6. An eraser covers the middle mark. Its height must be 4 because the surviving dots determine the line. In the classical code, any 1,023 numbered clues out of 1,048,577 determine the original note.

**Quantum image.** An illustrated strip of numbered signal slots has two flagged gaps. It illustrates how a receiver can know which signals went missing. The first quantum code can recover from any 1,023 missing carriers at known positions. The underlying construction works for infinitely many of the sizes in Ball and Vilar’s question.

## Evidence for the author

The straight line is a toy example. In the classical code, the message is a list of 1,023 coefficients. Each numbered clue is a scaled value of its polynomial, except for one special clue that gives the top coefficient. The receiver knows the clue numbers and scales. Any 1,023 intact clues uniquely determine the coefficient list. [Encoder and recovery theorem](../FullLength.lean)

A perfect spare copy of an arbitrary unknown quantum state is impossible. The quantum code distributes the information across many systems. It is a mathematical design for handling flagged losses. [Original no-cloning paper](https://doi.org/10.1038/299802a0)

Lean proves the classical encoder’s recovery guarantee and Hermitian self-orthogonality. The quantum parameters follow from the published Hermitian stabilizer construction. The quantum distance is 1,024. A code of that distance corrects 1,023 erasures at known locations, and this code meets the quantum Singleton bound. [Formal theorem](../FullLength.lean) · [Independent first-case check](../check_order25.py) · [Ball and Vilar, sections II and VII](https://arxiv.org/abs/2106.10180) · [Quantum Singleton bound and erasures](https://arxiv.org/abs/2010.07902)

Vilar listed the remaining even exponents in his 2025 thesis, chapter 7, p. 106. Our search identified no earlier construction covering these exact four classes. Independent confirmation of priority is pending. [Thesis](https://upcommons.upc.edu/server/api/core/bitstreams/3f9b47cc-9a24-4fd3-90a3-dd30e610a94c/content#page=107) · [Dated literature review](../../STATUS.md)
