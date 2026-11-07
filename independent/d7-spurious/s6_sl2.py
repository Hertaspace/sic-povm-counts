#!/usr/bin/env python3
"""Ordinary Clifford stabilizer arithmetic for d=7, independent of the spur certificates.

Checks:
- SL_2(F_7) element orders
- every order-3 element is conjugate to the Zauner matrix or its inverse
- the parity operator equals (1/7) sum_v D_v
- R D_v R = D_{-v}
- 8*(7*lambda-1)^2 is not a square for lambda = ±1
"""

from __future__ import annotations

# Locate dependencies relative to the public repository root.
from pathlib import Path as _EvidencePath
import sys as _evidence_sys
_evidence_sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError("Python optimization disables certificate assertions")
_evidence_root = next(p for p in _EvidencePath(__file__).resolve().parents
                      if (p / "replay" / "portable.py").is_file())
_evidence_sys.path.insert(0, str(_evidence_root / "replay"))
from portable import public_root, executable, resident_bytes

import json
from itertools import product
from pathlib import Path

OUT = public_root(__file__) / "independent/d7-spurious/out" / "s6_sl2.json"

# cyclotomic ints mod Phi_7, basis 1..w^5, coefficients in Z


def red(cs):
    a = [0] * 6
    for i, c in enumerate(cs):
        if c == 0:
            continue
        i %= 7
        if i == 6:
            for k in range(6):
                a[k] -= c
        else:
            a[i] += c
    return tuple(a)


def mul(u, v):
    raw = [0] * 12
    for i, a in enumerate(u):
        if a:
            for j, b in enumerate(v):
                if b:
                    raw[i + j] += a * b
    return red(raw)


def add(u, v):
    return tuple(u[i] + v[i] for i in range(6))


def smul(k, u):
    return tuple(k * x for x in u)


ZERO = (0, 0, 0, 0, 0, 0)
ONE = (1, 0, 0, 0, 0, 0)


def wpow(e):
    e %= 7
    if e == 0:
        return ONE
    if e < 6:
        xs = [0] * 6
        xs[e] = 1
        return tuple(xs)
    return tuple(-1 for _ in range(6))  # w^6 = -1-w-...-w^5


def mat_mul(A, B):
    n = len(A)
    C = [[ZERO for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k] == ZERO:
                continue
            for j in range(n):
                if B[k][j] != ZERO:
                    C[i][j] = add(C[i][j], mul(A[i][k], B[k][j]))
    return C


def D(i, j):
    """ACFW: D_(i,j) = tau^{ij} X^i Z^j, tau = w^4, X e_k = e_{k+1}, Z e_k = w^k e_k."""
    tau_pow = wpow(4 * i * j)
    M = [[ZERO for _ in range(7)] for _ in range(7)]
    for s in range(7):
        # (X^i Z^j e_s) = w^{j s} e_{s+i}, then times tau^{ij}
        row = (s + i) % 7
        M[row][s] = mul(tau_pow, wpow(j * s))
    return M


def parity():
    M = [[ZERO for _ in range(7)] for _ in range(7)]
    for k in range(7):
        M[(-k) % 7][k] = ONE
    return M


def sl2():
    G = []
    for a, b, c, d in product(range(7), repeat=4):
        if (a * d - b * c) % 7 == 1:
            G.append((a, b, c, d))
    return G


def mul_sl(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return ((a * e + b * g) % 7, (a * f + b * h) % 7, (c * e + d * g) % 7, (c * f + d * h) % 7)


def order(A):
    I = (1, 0, 0, 1)
    B = I
    for k in range(1, 400):
        B = mul_sl(B, A)
        if B == I:
            return k
    return None


def inv_sl(A):
    a, b, c, d = A
    # det 1, inverse is [[d, -b], [-c, a]]
    return (d % 7, (-b) % 7, (-c) % 7, a % 7)


def is_square(n):
    if n < 0:
        return False
    r = int(n**0.5)
    while r * r < n:
        r += 1
    while r * r > n:
        r -= 1
    return r * r == n


def main():
    G = sl2()
    orders = {}
    for A in G:
        k = order(A)
        orders[k] = orders.get(k, 0) + 1
    Fz = (0, 6, 1, 6)  # [[0, -1], [1, -1]]
    assert (Fz[0] * Fz[3] - Fz[1] * Fz[2]) % 7 == 1
    assert order(Fz) == 3
    Fz2 = mul_sl(Fz, Fz)
    # conjugacy: every order-3 element is conjugate to Fz or Fz^2
    order3 = [A for A in G if order(A) == 3]
    not_conjugate = []
    conj_to = {Fz: 0, Fz2: 0}
    for A in order3:
        hit = None
        for g in G:
            gi = inv_sl(g)
            if mul_sl(mul_sl(g, A), gi) == Fz:
                hit = Fz
                break
            if mul_sl(mul_sl(g, A), gi) == Fz2:
                hit = Fz2
                break
        if hit is None:
            not_conjugate.append(A)
        else:
            conj_to[hit] += 1

    # displacement identities
    R = parity()
    acc = [[ZERO for _ in range(7)] for _ in range(7)]
    for i in range(7):
        for j in range(7):
            M = D(i, j)
            for r in range(7):
                for c in range(7):
                    acc[r][c] = add(acc[r][c], M[r][c])
    # (1/7) sum D = R, so sum D = 7 R
    seven_R = [[smul(7, R[r][c]) for c in range(7)] for r in range(7)]
    sum_ok = acc == seven_R
    conj_fail = []
    for i in range(7):
        for j in range(7):
            left = mat_mul(mat_mul(R, D(i, j)), R)
            right = D((-i) % 7, (-j) % 7)
            # also the unreduced label (-i,-j). For d=7, tau^7=1 so D reduced equals D raw.
            raw = D(-i, -j) if False else None
            if left != right:
                conj_fail.append((i, j))
    # raw negative labels: D(-i,-j) built with negative exponents in the phase and the shift.
    # Our D() reduces i,j mod 7 in the shift (s+i)%7 and phase w^{4*i*j}. Check phase
    # w^{4*(-i)*(-j)} = w^{4 i j} and shift by -i equals shift by (-i)%7. So D(-i,-j)
    # as a function of integers equals D((-i)%7, (-j)%7) only if the phase exponent
    # 4*(-i)*(-j) and 4*((-i)%7)*((-j)%7) agree mod 7.
    phase_reduce_fail = []
    for i in range(7):
        for j in range(7):
            e_raw = (4 * (-i) * (-j)) % 7
            e_red = (4 * ((-i) % 7) * ((-j) % 7)) % 7
            if e_raw != e_red:
                phase_reduce_fail.append((i, j, e_raw, e_red))

    trace_obstruction = {}
    for lam in (1, -1):
        val = 8 * (7 * lam - 1) ** 2
        trace_obstruction[str(lam)] = {"value": val, "is_square": is_square(val)}

    # support lemma arithmetic: |S|<=2 cannot meet every nonzero difference;
    # |S|=3 forces u^2=1/8 and 3u=1.
    # recorded as an exact rational contradiction, not a search.
    #  (1/3)^2 = 1/9 != 1/8.
    three_support = (Q_eq())

    report = {
        "sl2_order": len(G),
        "order_counts": {str(k): v for k, v in sorted(orders.items())},
        "zauner": Fz,
        "zauner_order": order(Fz),
        "order3_count": len(order3),
        "order3_not_conjugate_to_zauner_class": len(not_conjugate),
        "conjugate_hits": {str(k): v for k, v in conj_to.items()},
        "sum_D_equals_7_parity": sum_ok,
        "parity_conjugates_D_to_minus": len(conj_fail) == 0,
        "parity_conjugate_failures": conj_fail[:8],
        "phase_reduction_mod_7_failures": phase_reduce_fail,
        "involution_trace_square_obstruction": trace_obstruction,
        "three_support_one_ninth_equals_one_eighth": three_support,
    }
    # fix the accidental call
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))


def Q_eq():
    return (1 / 9) != (1 / 8)


if __name__ == "__main__":
    main()
