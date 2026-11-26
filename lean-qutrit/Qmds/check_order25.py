"""Exhaustive independent check of the q = 1024 Ball–Vilar polynomial.

A bit at position i denotes the coefficient of X^i in the polynomial basis
of F_2[X]/(X^20 + X^3 + 1). Multiplication by X builds log/antilog tables.
The full cycle proves every nonzero residue is a unit in this quotient.
"""

from array import array


def verify():
    q = 1024
    field_size = q * q
    group_size = field_size - 1
    modulus = (1 << 20) | (1 << 3) | 1
    powers = array("I", [0]) * group_size
    logs = array("i", [-1]) * field_size

    value = 1
    for exponent in range(group_size):
        if value == 0 or logs[value] != -1:
            raise ValueError(f"Generator cycle stopped early at {exponent}")
        powers[exponent] = value
        logs[value] = exponent
        value <<= 1
        if value & field_size:
            value ^= modulus
    if value != 1:
        raise ValueError("Generator cycle failed to return to one")

    def power(x, n):
        if x == 0:
            return 1 if n == 0 else 0
        return powers[(logs[x] * n) % group_size]

    def multiply(x, y):
        if x == 0 or y == 0:
            return 0
        return powers[(logs[x] + logs[y]) % group_size]

    coefficient = powers[group_size // 25]
    if power(coefficient, 25) != 1 or power(coefficient, 5) == 1:
        raise ValueError("Coefficient failed the order-25 check")

    for x in range(field_size):
        g = multiply(coefficient, power(x, 205))
        value = 1 ^ power(x, 1025) ^ g ^ power(g, 1024)
        if value == 0:
            raise ValueError(f"Root at x={x:#x}")

    print(f"q={q}, e={coefficient:#x}, order=25, "
          f"{field_size} field elements checked, zero roots")


if __name__ == "__main__":
    verify()
