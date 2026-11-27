# My dot joined the theorem party

## Opening post

I gave my dot three math problems. On the quantum one, a single bad input out of 268,435,456 would wreck the answer.

The first 207 settings all broke. Setting 208 held.

Then came the surprise. We could prove the same trick works at infinitely many sizes. 🧵

Attach the [208-settings graphic](../../../harness/setting-208.png).

## Reply 1

What’s the prize? Imagine sending a quantum message in 268,435,457 pieces. Any 16,383 can vanish. If you know which ones went missing, the message can still be recovered. The math gives a design that reaches the limit for how much information it carries.

## Reply 2

Grassl and Rötteler had five examples in 2015. Ball and Vilar cracked the odd exponents in 2021. Vilar still listed the larger even ones as open in 2025. Lean checked our classical code for four infinite groups of even exponents, starting at q = 16,384. https://arxiv.org/abs/2106.10180

## Reply 3

Why did the search take half a second? We found a way to sort those 268 million inputs by radius and direction. There were only five directions to worry about. Setting 1 failed at nine radii. Setting 208 failed at zero. A second program checked the count a different way.

## Reply 4

Same harness, two more hunts. On Shannon’s seven-symbol code we reproduced a known dead end. Swapping up to five words still leaves you stuck at 367. On the sixth-power puzzle we searched one family through a million and found no identity. Both big questions are still open.

## Reply 5

Three short searches took about six seconds together. Designing them and proving the answer took longer. You can rerun the search for 208, the independent check and the Lean proof. Know an earlier construction for q = 16,384? I’d love the citation. https://github.com/anzal1/research/blob/4180e3ff0978047e8a4dc58f877ff6206f31aee2/lean-qutrit/Qmds/Order29.lean

## Evidence and image description

The graphic shows 208 settings in numerical order, with one dot per setting. The independent checker enumerates all radii for five directions and finds a failure for every setting from 1 through 207. Setting 208 has zero. Each setting encodes a scale in a specified trace basis. The first quantum-code alphabet has 16,384 levels. A code position is a carrier, and the loss guarantee counts carriers at known positions. The kernel theorem is the Hermitian self-orthogonal classical MDS construction. The quantum erasure guarantee follows from the published stabilizer construction. The five-deletion extension has a separate timing from the short three-search benchmark.

Historical priority remains open. The sources checked give a dated open question and yielded no earlier matching solution. [Mathematical statement and literature audit](../ORDER29.md) · [Runner and timings](../../../harness/README.md) · [Vilar’s thesis, p. 106](https://tesisenred.net/bitstream/handle/10803/694186/TRVA1de1.pdf?isAllowed=y&sequence=1#page=107)
