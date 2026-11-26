"""Independent additive stabilizer check using the repository's GF(3) elimination."""
import itertools
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "qutrit-eaqecc"))
from check_degenerate import nullspace_f3, rank_f3, swt, symp


def flatten(pairs):
    return [x % 3 for x, z in pairs] + [z % 3 for x, z in pairs]


def remainder(coeff, modulus):
    """Reduce a polynomial by a monic quadratic, low-degree coefficient first."""
    out = list(coeff)
    for k in (3, 2):
        for j in range(2):
            out[k - 2 + j] -= out[k] * modulus[j]
    return tuple(t % 3 for t in out[:2])


def cubic_row(coeff):
    _, b, c, d = coeff
    pairs = []
    for t, scale in [(0, 1), (1, 1), (-1, -1)]:
        value = sum(v * t**i for i, v in enumerate(coeff))
        deriv = b + 2 * c * t + 3 * d * t**2
        pairs.extend([(value, scale * deriv), (value, 0)])
    pairs.extend([(d, c), (d, 0)])
    for modulus in [(1, 0), (2, 1)]:
        x, z = remainder(coeff, modulus)
        pairs.extend([(x, z), (x, -z)])
    return flatten(pairs)


n = 12
rows = [cubic_row([int(i == k) for i in range(4)]) for k in range(4)]
for k in range(4):
    pairs = [(0, 0)] * n
    pairs[2*k : 2*k+2] = [(0, 1), (0, -1)]
    rows.append(flatten(pairs))

# Take the symplectic dual and then its dual again. Enumerate the latter in
# the basis produced by elimination, independent of the pair construction.
def dual(basis):
    return nullspace_f3([[(-z) % 3 for z in row[n:]] + row[:n] for row in basis], 2 * n)


s = dual(rows)
normalizer = dual(s)
gram_rank = rank_f3([[symp(x, y, n) for y in s] for x in s])
hist = Counter()
for coeff in itertools.product(range(3), repeat=len(normalizer)):
    word = [sum(c * t for c, t in zip(coeff, col)) % 3 for col in zip(*normalizer)]
    if any(symp(word, row, n) for row in normalizer):
        hist[swt(word, n)] += 1

assert (len(normalizer), len(s), gram_rank) == (8, 16, 12)
assert hist == {9: 1488, 10: 1152, 11: 1440, 12: 2400}
print(f"dim N = {len(normalizer)}, dim S = {len(s)}, rank Gram(S) = {gram_rank}")
print("non-radical weight distribution", sorted(hist.items()))
