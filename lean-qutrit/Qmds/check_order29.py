"""Independent first-case check in GF(2^28) using the 29th cyclotomic polynomial.

The search uses degree-14 logarithm tables and a degree-25 radial polynomial.
This implementation instead enumerates angular traces and every base-field radius.
"""
from collections import Counter

Q = 16384
PHI29 = (1 << 29) - 1


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a >> 28:
            a ^= PHI29
        b >>= 1
    return result


def power(a, n):
    result = 1
    while n:
        if n & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        n >>= 1
    return result


def generator(order, primes):
    for base in range(2, Q):
        g = power(base, (Q * Q - 1) // order)
        if power(g, order) == 1 and all(power(g, order // p) != 1 for p in primes):
            return g
    raise ValueError(f"Missing element of order {order}")


def check():
    # For prime 29 the cyclotomic polynomial is irreducible since ord_29(2)=28.
    assert pow(2, 28, 29) == 1 and all(pow(2, 28 // p, 29) != 1 for p in (2, 7))
    w = 2
    assert power(w, 29) == 1 and w != 1
    t = w ^ power(w, Q)
    v = generator(5, (5,))
    angles = [multiply(w, power(v, k)) for k in range(5)]
    traces = {a ^ power(a, Q) for a in angles}
    assert len(traces) == 5
    g = generator(Q - 1, (3, 43, 127))
    g4, ginv = power(g, 4), power(g, Q - 2)
    z4 = zinv = 1
    frequencies = Counter()
    example_inverse = {}
    for _ in range(Q - 1):
        value = z4 ^ zinv
        frequencies[value] += 1
        example_inverse[value] = zinv
        z4 = multiply(z4, g4)
        zinv = multiply(zinv, ginv)
    assert z4 == zinv == 1
    d = (Q+1)//5
    failures = []
    for setting in range(1, 209):
        scale = 0
        for bit in range(setting.bit_length()):
            if setting & (1 << bit):
                scale ^= power(t, bit)
        assert power(scale, Q) == scale and scale
        failures.append(sum(frequencies[multiply(scale, trace)] for trace in traces))
        if failures[-1]:
            for k, a in enumerate(angles):
                value = multiply(scale, a ^ power(a, Q))
                if value in example_inverse:
                    # Recover x with x=y*u, y^d=z and u^d=v^k.
                    y = power(example_inverse[value], (-pow(d, -1, Q-1)) % (Q-1))
                    u = power(v, (k * pow(d, -1, 5)) % 5)
                    x = multiply(y, u)
                    term = multiply(multiply(scale, w), power(x, d))
                    assert 1 ^ power(x, Q+1) ^ term ^ power(term, Q) == 0
                    break
    assert all(failures[:-1]) and failures[-1] == 0 and failures[0] == 9
    print(f"GF(2^28): {Q-1} radii, {len(traces)} angles, zero roots; "
          f"scale-one control hits {failures[0]} radii; H(0)=1")
    return failures


if __name__ == "__main__":
    check()
