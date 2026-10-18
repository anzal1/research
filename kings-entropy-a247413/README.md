# King's graph entropy constant (OEIS A247413) to 26 digits

**Result:** the hard-core lattice gas constant on the king's graph is

    kappa = 1.3426439511246012978517301...

That is 26 correct digits. OEIS [A247413](https://oeis.org/A247413) had 18, so this adds a(19) to a(26) = 7, 8, 5, 1, 7, 3, 0, 1.

**Status:** submitted to OEIS on 2026-10-18, now in editor review.

## What the constant is

Count the ways to place non-attacking kings on an n by n board. That count grows like kappa^(n^2). OEIS [A063443](https://oeis.org/A063443) lists the counts and A247413 lists the digits of kappa. No closed form is known.

## How it was computed

`compute_a247413.c` runs a row-to-row transfer-matrix renormalization (TMRG) in 75-digit decimal arithmetic. It prints the estimate for bond dimensions m = 16, 18, 20, 22 and 24. The first 26 digits are the same for every m from 18 up, which is the evidence for those digits.

A separate corner transfer matrix computation, not included here, agreed with it to about 1e-28. The two methods are close relatives, so treat this as a careful numerical result, not a proof.

## Run it yourself

You need the free `mpdecimal` library (`brew install mpdecimal` on macOS, `apt install libmpdec-dev` on Debian or Ubuntu).

    cc -O2 compute_a247413.c -lmpdec -o compute_a247413
    ./compute_a247413

It takes a few minutes on one core. Compare with `expected_output.txt`. The CI job in this repo runs it on every push and fails if the 26 digits ever change.

## Prior work

- Vaclav Kotesovec, A247413 (2014), first 13 digits.
- Kai Liang, [arXiv:2505.12776](https://arxiv.org/abs/2505.12776) (2025), digits 14 to 18.
