#!/usr/bin/env python3
"""Independent killer check of the d=7 lower bound of 32928 points.

Does not import or replay e301. Seeds are the formulas in
the exact projector formulas documented in PROOFS/d7.md.
Displacement operators follow ACFW (arXiv:1703.05981 §2):
    tau = zeta^4,  omega = zeta,  D_(p1,p2) = tau^(p1*p2) X^p1 Z^p2,
with zeta a primitive 7th root. For d=7 one has tau^7 = 1.

P1 is exact arithmetic in the 48-dimensional tower.
P2 enumerates the projective Clifford group over two primes.
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

import itertools
import json
import math
import time
from fractions import Fraction

# ---------------------------------------------------------------------------
# Tower Q(s)(r)(i)(zeta). Relations:
#   s^2 = 2,  r^2 = s - 1/2,  i^2 = -1,  Phi_7(zeta) = 0.
# ---------------------------------------------------------------------------


class QS:
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = a if isinstance(a, Fraction) else Fraction(a)
        self.b = b if isinstance(b, Fraction) else Fraction(b)

    def __repr__(self):
        return f"QS({self.a},{self.b})"

    def is_zero(self):
        return self.a == 0 and self.b == 0

    def __eq__(self, other):
        return isinstance(other, QS) and self.a == other.a and self.b == other.b

    def __neg__(self):
        return QS(-self.a, -self.b)

    def __add__(self, other):
        if not isinstance(other, QS):
            other = QS(other, 0)
        return QS(self.a + other.a, self.b + other.b)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, QS):
            other = QS(other, 0)
        a, b, c, d = self.a, self.b, other.a, other.b
        return QS(a * c + 2 * b * d, a * d + b * c)

    def __rmul__(self, other):
        return self * other

    def norm(self):
        return self.a * self.a - 2 * self.b * self.b

    def inv(self):
        n = self.norm()
        if n == 0:
            raise ZeroDivisionError("QS norm 0")
        return QS(self.a / n, -self.b / n)

    def __truediv__(self, other):
        if not isinstance(other, QS):
            other = QS(other, 0)
        return self * other.inv()


class QSR:
    __slots__ = ("p", "q")

    def __init__(self, p=None, q=None):
        self.p = p if isinstance(p, QS) else QS(0 if p is None else p, 0)
        self.q = q if isinstance(q, QS) else QS(0 if q is None else q, 0)

    def is_zero(self):
        return self.p.is_zero() and self.q.is_zero()

    def __eq__(self, other):
        return isinstance(other, QSR) and self.p == other.p and self.q == other.q

    def __neg__(self):
        return QSR(-self.p, -self.q)

    def __add__(self, other):
        if not isinstance(other, QSR):
            other = QSR(QS(other, 0), QS(0, 0))
        return QSR(self.p + other.p, self.q + other.q)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, QSR):
            other = QSR(QS(other, 0), QS(0, 0))
        # r^2 = s - 1/2
        r2 = QS(Fraction(-1, 2), 1)
        p = self.p * other.p + self.q * other.q * r2
        q = self.p * other.q + self.q * other.p
        return QSR(p, q)

    def __rmul__(self, other):
        return self * other

    def norm(self):
        r2 = QS(Fraction(-1, 2), 1)
        return self.p * self.p - self.q * self.q * r2

    def inv(self):
        n = self.norm()
        if n.is_zero():
            raise ZeroDivisionError("QSR norm 0")
        ni = n.inv()
        return QSR(self.p * ni, -(self.q * ni))

    def __truediv__(self, other):
        if not isinstance(other, QSR):
            other = QSR(QS(other, 0), QS(0, 0))
        return self * other.inv()


class QSRI:
    __slots__ = ("u", "v")

    def __init__(self, u=None, v=None):
        self.u = u if isinstance(u, QSR) else QSR(QS(0 if u is None else u), QS(0))
        self.v = v if isinstance(v, QSR) else QSR(QS(0 if v is None else v), QS(0))

    def is_zero(self):
        return self.u.is_zero() and self.v.is_zero()

    def __eq__(self, other):
        return isinstance(other, QSRI) and self.u == other.u and self.v == other.v

    def __neg__(self):
        return QSRI(-self.u, -self.v)

    def __add__(self, other):
        if not isinstance(other, QSRI):
            other = QSRI(QSR(QS(other)), QSR(QS(0)))
        return QSRI(self.u + other.u, self.v + other.v)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, QSRI):
            other = QSRI(QSR(QS(other)), QSR(QS(0)))
        u = self.u * other.u - self.v * other.v
        v = self.u * other.v + self.v * other.u
        return QSRI(u, v)

    def __rmul__(self, other):
        return self * other

    def conj_i(self):
        return QSRI(self.u, -self.v)

    def norm(self):
        return self.u * self.u + self.v * self.v

    def inv(self):
        n = self.norm()
        if n.is_zero():
            raise ZeroDivisionError("QSRI norm 0")
        ni = n.inv()
        return QSRI(self.u * ni, -(self.v * ni))

    def __truediv__(self, other):
        if not isinstance(other, QSRI):
            other = QSRI(QSR(QS(other)), QSR(QS(0)))
        return self * other.inv()

    def expand(self):
        """Return 8 Fractions on basis s^es r^er i^ei, es,er,ei in {0,1}."""
        out = [Fraction(0)] * 8

        def add_qsr(base_ei, qsr, sign=1):
            # qsr = (a+bs) + (c+ds) r
            a, b = qsr.p.a, qsr.p.b
            c, d = qsr.q.a, qsr.q.b
            out[base_ei * 4 + 0] += sign * a
            out[base_ei * 4 + 1] += sign * b
            out[base_ei * 4 + 2] += sign * c
            out[base_ei * 4 + 3] += sign * d

        add_qsr(0, self.u, 1)
        add_qsr(1, self.v, 1)
        return out


def qs_from_expand_pair(a, b):
    return QS(a, b)


class Cyc:
    __slots__ = ("c",)

    def __init__(self, coeffs=None):
        if coeffs is None:
            self.c = tuple(QSRI() for _ in range(6))
        else:
            self.c = tuple(coeffs)

    @staticmethod
    def const(x):
        if not isinstance(x, QSRI):
            if isinstance(x, QSR):
                x = QSRI(x, QSR())
            elif isinstance(x, QS):
                x = QSRI(QSR(x, QS(0)), QSR())
            else:
                x = QSRI(QSR(QS(x), QS(0)), QSR())
        z = [QSRI() for _ in range(6)]
        z[0] = x
        return Cyc(z)

    @staticmethod
    def zeta(k=1):
        z = [QSRI() for _ in range(6)]
        k %= 7
        if k == 0:
            z[0] = QSRI(QSR(QS(1), QS(0)), QSR())
            return Cyc(z)
        if k == 6:
            one = QSRI(QSR(QS(1), QS(0)), QSR())
            for j in range(6):
                z[j] = -one
            return Cyc(z)
        z[k] = QSRI(QSR(QS(1), QS(0)), QSR())
        return Cyc(z)

    def is_zero(self):
        return all(t.is_zero() for t in self.c)

    def __eq__(self, other):
        if not isinstance(other, Cyc):
            other = Cyc.const(other)
        return self.c == other.c

    def __neg__(self):
        return Cyc(tuple(-t for t in self.c))

    def __add__(self, other):
        if not isinstance(other, Cyc):
            other = Cyc.const(other)
        return Cyc(tuple(x + y for x, y in zip(self.c, other.c)))

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Cyc):
            other = Cyc.const(other)
        acc = [QSRI() for _ in range(6)]

        def add_pow(exp, val):
            exp %= 7
            if val.is_zero():
                return
            if exp == 6:
                for j in range(6):
                    acc[j] = acc[j] - val
            else:
                acc[exp] = acc[exp] + val

        for i, ai in enumerate(self.c):
            if ai.is_zero():
                continue
            for j, bj in enumerate(other.c):
                if bj.is_zero():
                    continue
                add_pow(i + j, ai * bj)
        return Cyc(acc)

    def __rmul__(self, other):
        return self * other

    def conj(self):
        """Complex conjugation of the standard embedding: i->-i, zeta->zeta^{-1}, s,r fixed."""
        acc = [QSRI() for _ in range(6)]

        def add_pow(exp, val):
            exp %= 7
            if val.is_zero():
                return
            if exp == 6:
                for j in range(6):
                    acc[j] = acc[j] - val
            else:
                acc[exp] = acc[exp] + val

        # coeff of zeta^0
        acc[0] = self.c[0].conj_i()
        # zeta^{-1} = zeta^6 = -sum_{0..5} zeta^j
        g1 = self.c[1].conj_i()
        if not g1.is_zero():
            for j in range(6):
                acc[j] = acc[j] - g1
        # zeta^{-2}=zeta^5, zeta^{-3}=zeta^4, zeta^{-4}=zeta^3, zeta^{-5}=zeta^2
        acc[5] = acc[5] + self.c[2].conj_i()
        acc[4] = acc[4] + self.c[3].conj_i()
        acc[3] = acc[3] + self.c[4].conj_i()
        acc[2] = acc[2] + self.c[5].conj_i()
        return Cyc(acc)

    def expand48(self):
        out = [Fraction(0)] * 48
        for ez, coeff in enumerate(self.c):
            block = coeff.expand()
            for t, val in enumerate(block):
                if val:
                    out[ez + 6 * t] = val
        return out


def S_elem():
    return QS(0, 1)


def R_elem():
    return QSR(QS(0), QS(1))


def I_elem():
    return QSRI(QSR(QS(0), QS(0)), QSR(QS(1), QS(0)))


def gauss_sum():
    # G = z + z^2 - z^3 + z^4 - z^5 - z^6
    acc = Cyc.const(0)
    signs = {1: 1, 2: 1, 3: -1, 4: 1, 5: -1, 6: -1}
    for k, s in signs.items():
        acc = acc + Cyc.const(s) * Cyc.zeta(k)
    return acc


def r_minus(G, r):
    return G / Cyc.const(QSR(QS(2), QS(0)) * r)


# ---------------------------------------------------------------------------
# Seeds and Z
# ---------------------------------------------------------------------------


def zpow(e):
    return Cyc.zeta(e)


def displacement_overlap(b, a, p1, p2):
    """Z = b^T D_(p1,p2) a, ACFW. Indices 0..6."""
    p1 %= 7
    p2 %= 7
    tau_phase = zpow(4 * p1 * p2)  # tau = zeta^4, tau^7 = 1
    acc = Cyc.const(0)
    for j in range(7):
        src = (j - p1) % 7
        w = tau_phase * zpow(p2 * (j - p1)) * b[j] * a[src]
        acc = acc + w
    return acc


def q_report(a, b):
    z0 = Cyc.const(0)
    for j in range(7):
        z0 = z0 + b[j] * a[j]
    bad = []
    reps = []
    seen = set()
    for i, j in itertools.product(range(7), repeat=2):
        if (i, j) == (0, 0):
            continue
        key = tuple(sorted([(i, j), ((-i) % 7, (-j) % 7)]))
        if key in seen:
            continue
        seen.add(key)
        reps.append((i, j))
    assert len(reps) == 24
    for p1, p2 in reps:
        zp = displacement_overlap(b, a, p1, p2)
        zm = displacement_overlap(b, a, -p1, -p2)
        # 8 Z(p)Z(-p) - Z(0)^2
        delta = zp * zm * 8 - z0 * z0
        if not delta.is_zero():
            bad.append((p1, p2))
    herm = hermitian(a, b)
    return {
        "Z0_is_one": z0 == Cyc.const(1),
        "Z0_zero": z0.is_zero(),
        "q_bad": bad,
        "n_reps": len(reps),
        "hermitian": herm,
        "support_zeta": zeta_support(a, b),
    }


def hermitian(a, b):
    ga = [x.conj() for x in a]
    # minors b_i ga_j - b_j ga_i
    for i in range(7):
        for j in range(i + 1, 7):
            if not (b[i] * ga[j] - b[j] * ga[i]).is_zero():
                return False
    # nontrivial
    if all(x.is_zero() for x in b) or all(x.is_zero() for x in ga):
        return False
    return True


def zeta_support(a, b):
    used = set()
    for v in list(a) + list(b):
        for k, c in enumerate(v.c):
            if not c.is_zero():
                used.add(k)
    return sorted(used)


def vec_to_cyc(xs):
    return [x if isinstance(x, Cyc) else Cyc.const(x) for x in xs]


def family1(ss, rr):
    # ss, rr are Cyc (or embedded)
    ii = Cyc.const(I_elem())
    one = Cyc.const(1)
    et = one + ii * (ss * 2 - 1)
    kap = -one + ss * Fraction(1, 2)
    N = Cyc.const(16) - ss * 4
    u = div_qsri_scalar(kap - rr, et)
    v = div_qsri_scalar(kap + rr, et)
    cc = div_qsri_scalar(Cyc.const(10) - ss * 4, N)
    e = div_qsri_scalar(et * (kap - rr), N)
    f = div_qsri_scalar(et * (kap + rr), N)
    x = [one, u, u, v, u, v, v]
    y = [cc, e, e, f, e, f, f]
    return x, y


def as_qsri_const(elem):
    """If elem is constant in zeta, return the QSRI. Else None."""
    if any(not elem.c[k].is_zero() for k in range(1, 6)):
        return None
    return elem.c[0]


def div_qsri_scalar(numer, denom):
    """Divide Cyc by a zeta-constant denominator living in QSRI, or a general Cyc constant."""
    d = as_qsri_const(denom)
    if d is None:
        raise NotImplementedError("non-constant denominator")
    invd = d.inv()
    return numer * Cyc.const(invd)


def family2(ss, rr):
    one = Cyc.const(1)
    t = ss * rr
    u = (-one - ss + t) * Fraction(1, 2)
    v = (-one - ss - t) * Fraction(1, 2)
    cc = div_qsri_scalar(one, Cyc.const(4) + ss * 6)
    x = [one, u, u, v, u, v, v]
    y = [cc * xj for xj in x]
    return x, y


def quartic_residuals(x, y):
    bad = []
    for a in range(7):
        for b in range(7):
            acc = Cyc.const(0)
            for j in range(7):
                acc = acc + x[j] * y[(j + a) % 7] * y[(j + b) % 7] * x[(j + a + b) % 7]
            acc = acc * 8
            if a == 0:
                acc = acc - 1
            if b == 0:
                acc = acc - 1
            if not acc.is_zero():
                bad.append((a, b))
    return bad


def doubly_symmetric(v):
    return all((v[(2 * j) % 7] - v[j]).is_zero() for j in range(7))


# ---------------------------------------------------------------------------
# Clifford generators over Q(zeta), exact covariance of q
# ---------------------------------------------------------------------------


def mat_mul(A, B):
    n = 7
    C = [[Cyc.const(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k].is_zero():
                continue
            for j in range(n):
                if not B[k][j].is_zero():
                    C[i][j] = C[i][j] + A[i][k] * B[k][j]
    return C


def mat_vec(A, v):
    out = []
    for i in range(7):
        acc = Cyc.const(0)
        for j in range(7):
            if not A[i][j].is_zero() and not v[j].is_zero():
                acc = acc + A[i][j] * v[j]
        out.append(acc)
    return out


def eye_cyc():
    return [[Cyc.const(1 if i == j else 0) for j in range(7)] for i in range(7)]


def D_matrix(p1, p2):
    p1 %= 7
    p2 %= 7
    M = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    phase = zpow(4 * p1 * p2)
    for col in range(7):
        M[(col + p1) % 7][col] = phase * zpow(p2 * col)
    return M


def mat_eq(A, B):
    return all((A[i][j] - B[i][j]).is_zero() for i in range(7) for j in range(7))


def mat_scale(A, s):
    return [[A[i][j] * s for j in range(7)] for i in range(7)]


def transpose(A):
    return [[A[j][i] for j in range(7)] for i in range(7)]


def generators_exact():
    """Return list of (name, U, W) with W = U^{-T}."""
    z = Cyc.zeta(1)
    # X: (Xv)_j = v_{j-1}
    X = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    for j in range(7):
        X[j][(j - 1) % 7] = Cyc.const(1)
    # Z diagonal zeta^j
    Z = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    WZ = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    for j in range(7):
        Z[j][j] = zpow(j)
        WZ[j][j] = zpow(-j)
    # S diagonal tau^{j^2} = zeta^{4 j^2}
    S = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    WS = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    for j in range(7):
        S[j][j] = zpow(4 * j * j)
        WS[j][j] = zpow(-4 * j * j)
    # Fourier unnormalized
    F = [[zpow(j * k) for k in range(7)] for j in range(7)]
    inv7 = Cyc.const(Fraction(1, 7))
    WF = [[zpow(-j * k) * inv7 for k in range(7)] for j in range(7)]
    return [
        ("X", X, X),  # X^{-T} = X
        ("Z", Z, WZ),
        ("S", S, WS),
        ("F", F, WF),
    ]


def identify_displacement(M):
    """If M = chi * D_(p1,p2), return (p1,p2,chi). Else None."""
    shifts = set()
    entries = []
    for col in range(7):
        rows = [r for r in range(7) if not M[r][col].is_zero()]
        if len(rows) != 1:
            return None
        r = rows[0]
        shifts.add((r - col) % 7)
        entries.append(M[r][col])
    if len(shifts) != 1:
        return None
    p1 = shifts.pop()
    # ratio entry1/entry0 = omega^{p2}
    if entries[0].is_zero():
        return None
    # Compare entries[1] * entries[0] inverse. entries are monomials in zeta, constant over QSRI.
    # Solve by testing p2.
    found = None
    for p2 in range(7):
        phase = zpow(4 * p1 * p2)
        # predicted entry at column 0: chi * phase * omega^0, so chi = entries[0] / phase
        # Check all columns against chi * D
        # column col value should be chi * phase * z^{p2*col}
        ok = True
        # chi candidate from col 0: entries[0] should equal chi * phase, chi = entries[0] * phase^{-1}
        # phase is a zeta power; multiply by inverse zeta power.
        inv_phase = zpow(-(4 * p1 * p2))
        chi = entries[0] * inv_phase
        for col in range(7):
            pred = chi * phase * zpow(p2 * col)
            if not (M[(col + p1) % 7][col] - pred).is_zero():
                ok = False
                break
            for r in range(7):
                if r != (col + p1) % 7 and not M[r][col].is_zero():
                    ok = False
                    break
            if not ok:
                break
        if ok:
            found = (p1, p2, chi)
            break
    return found


def check_generator_covariance():
    """Each generator satisfies U^{-1} D_p U = chi(p) D_{sigma p} with chi(p)chi(-p)=1."""
    report = []
    I = eye_cyc()
    for name, U, W in generators_exact():
        # W should be U^{-T}, so U * W^T = I
        prod = mat_mul(U, transpose(W))
        if not mat_eq(prod, I):
            report.append({"name": name, "inverse_ok": False})
            continue
        images = {}
        chi_ok = True
        bad_id = []
        for p1, p2 in itertools.product(range(7), repeat=2):
            # U^{-1} D U = W^T * D * U
            M = mat_mul(transpose(W), mat_mul(D_matrix(p1, p2), U))
            ident = identify_displacement(M)
            if ident is None:
                bad_id.append((p1, p2))
                continue
            q1, q2, chi = ident
            images[(p1, p2)] = (q1, q2, chi)
        for p1, p2 in images:
            q1, q2, chi = images[(p1, p2)]
            mq = ((-p1) % 7, (-p2) % 7)
            if mq not in images:
                chi_ok = False
                continue
            _a, _b, chi_m = images[mq]
            if not (chi * chi_m - 1).is_zero():
                chi_ok = False
        # sigma linearity on a basis
        if (1, 0) in images and (0, 1) in images and (1, 1) in images:
            e1 = images[(1, 0)][:2]
            e2 = images[(0, 1)][:2]
            s11 = images[(1, 1)][:2]
            linear = (s11[0] - (e1[0] + e2[0]) % 7 == 0) and (s11[1] - (e1[1] + e2[1]) % 7 == 0)
            # rebuild matrix [[e1_x, e2_x],[e1_y, e2_y]]? 
            # sigma(x,y) = x*sigma(1,0)+y*sigma(0,1)
            # The matrix acts on column vectors (p1,p2). sigma(p) = M p.
            # columns of M are sigma(e1), sigma(e2).
            Msl = [[e1[0], e2[0]], [e1[1], e2[1]]]
            det = (Msl[0][0] * Msl[1][1] - Msl[0][1] * Msl[1][0]) % 7
        else:
            linear = False
            Msl = None
            det = None
        report.append(
            {
                "name": name,
                "inverse_ok": True,
                "unidentified": bad_id,
                "chi_pair_ok": chi_ok,
                "linear_11": linear,
                "sl_matrix": Msl,
                "det": det,
                "n_images": len(images),
            }
        )
    return report


def permutation_zauner():
    """P e_j = e_{2j}, so (Pv)_j = v_{4j}. Integer matrix, order 3."""
    P = [[Cyc.const(0) for _ in range(7)] for _ in range(7)]
    for j in range(7):
        P[j][(4 * j) % 7] = Cyc.const(1)
    return P


# ---------------------------------------------------------------------------
# Finite-field Clifford group
# ---------------------------------------------------------------------------


def matmul_p(A, B, p):
    C = [[0] * 7 for _ in range(7)]
    for i in range(7):
        Ai = A[i]
        Ci = C[i]
        for k in range(7):
            aik = Ai[k]
            if aik == 0:
                continue
            Bk = B[k]
            for j in range(7):
                Ci[j] = (Ci[j] + aik * Bk[j]) % p
    return C


def matvec_p(A, v, p):
    return [sum(A[i][j] * v[j] for j in range(7)) % p for i in range(7)]


def transpose_p(A):
    return [[A[j][i] for j in range(7)] for i in range(7)]


def scale_p(A, s, p):
    return tuple(tuple((A[i][j] * s) % p for j in range(7)) for i in range(7))


def normalize_pair(U, W, p):
    for i in range(7):
        for j in range(7):
            uij = U[i][j] % p
            if uij:
                inv = pow(uij, -1, p)
                return scale_p(U, inv, p), scale_p(W, uij, p)
    raise ZeroDivisionError("singular")


def D_matrix_p(p1, p2, z, p):
    p1 %= 7
    p2 %= 7
    M = [[0] * 7 for _ in range(7)]
    phase = pow(z, (4 * p1 * p2) % 7, p)
    for col in range(7):
        M[(col + p1) % 7][col] = phase * pow(z, (p2 * col) % 7, p) % p
    return M


def generators_p(z, p):
    X = [[0] * 7 for _ in range(7)]
    for j in range(7):
        X[j][(j - 1) % 7] = 1
    Z = [[0] * 7 for _ in range(7)]
    WZ = [[0] * 7 for _ in range(7)]
    for j in range(7):
        Z[j][j] = pow(z, j, p)
        WZ[j][j] = pow(z, (-j) % 7, p)
    S = [[0] * 7 for _ in range(7)]
    WS = [[0] * 7 for _ in range(7)]
    for j in range(7):
        S[j][j] = pow(z, (4 * j * j) % 7, p)
        WS[j][j] = pow(z, (-4 * j * j) % 7, p)
    F = [[pow(z, (j * k) % 7, p) for k in range(7)] for j in range(7)]
    inv7 = pow(7, -1, p)
    WF = [[pow(z, (-j * k) % 7, p) * inv7 % p for k in range(7)] for j in range(7)]
    raw = [("X", X, X), ("Z", Z, WZ), ("S", S, WS), ("F", F, WF)]
    out = []
    for name, U, W in raw:
        # also inverse, derived from W: Uinv = W^T, and (Uinv)^{-T} = U^T
        Uinv = transpose_p(W)
        Winv = transpose_p(U)
        out.append((name, U, W))
        out.append((name + "inv", Uinv, Winv))
    return out


def prod_is_I(U, W, p):
    M = matmul_p(U, transpose_p(W), p)
    return all(M[i][j] % p == (1 if i == j else 0) for i in range(7) for j in range(7))


def build_group(z, p):
    gens = generators_p(z, p)
    for name, U, W in gens:
        if not prod_is_I(U, W, p):
            raise RuntimeError(f"generator {name} fails U W^T = I")
    eye = [[1 if i == j else 0 for j in range(7)] for i in range(7)]
    U0, W0 = normalize_pair(eye, eye, p)
    seen = {U0: W0}
    parent = {U0: None}
    how = {U0: None}
    queue = [U0]
    qi = 0
    while qi < len(queue):
        if len(seen) > 20000:
            raise RuntimeError(f"group enumeration exceeded 20000 at p={p}")
        U = queue[qi]
        W = seen[U]
        qi += 1
        for gi, (name, G, GW) in enumerate(gens):
            # U_new = U*G, W_new = W*GW = U_new^{-T}. The opposite W order
            # breaks U W^T = I as soon as two noncommuting factors appear.
            U2 = matmul_p(U, G, p)
            W2 = matmul_p(W, GW, p)
            Un, Wn = normalize_pair(U2, W2, p)
            if Un not in seen:
                seen[Un] = Wn
                parent[Un] = U
                how[Un] = gi
                queue.append(Un)
    bad_inv = sum(1 for U, W in seen.items() if not prod_is_I(U, W, p))
    if bad_inv:
        raise RuntimeError(f"{bad_inv} group elements fail U W^T = I")
    return {
        "gens": gens,
        "U_to_W": seen,
        "order": len(seen),
        "parent": parent,
        "how": how,
    }


def norm_vec(v, p):
    for i, x in enumerate(v):
        if x % p:
            inv = pow(x % p, -1, p)
            return tuple((y * inv) % p for y in v)
    return None


def apply_point(U, W, pt, p):
    a, b = pt
    return norm_vec(matvec_p(U, a, p), p), norm_vec(matvec_p(W, b, p), p)


def point_key(pt):
    return pt


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q = p - 1
    s = 0
    while q % 2 == 0:
        s += 1
        q //= 2
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m = s
    c = pow(z, q, p)
    t = pow(a, q, p)
    r = pow(a, (q + 1) // 2, p)
    while t != 1:
        i = 1
        t2 = (t * t) % p
        while t2 != 1:
            t2 = (t2 * t2) % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        r = (r * b) % p
        c = (b * b) % p
        t = (t * c) % p
        m = i
    return r


def find_hom(p):
    """A ring hom of the tower into F_p. Returns images of s,r,i,z."""
    roots = [x for x in range(p) if (4 * pow(x, 4, p) + 4 * pow(x, 2, p) - 7) % p == 0]
    if len(roots) < 1:
        return None
    r = roots[0]
    inv2 = pow(2, -1, p)
    s = (r * r + inv2) % p
    if (s * s - 2) % p:
        return None
    ii = sqrt_mod(p - 1, p)
    if ii is None:
        return None
    zs = [t for t in range(1, p) if pow(t, 7, p) == 1 and t != 1]
    # keep those with Phi_7 = 0, automatic for order 7
    if not zs:
        return None
    return {"s": s, "r": r, "i": ii, "z": zs[0], "quartic_roots": len(roots)}


def reduce_cyc(elem, hom, p):
    acc = 0
    coeffs = elem.expand48()
    z, s, r, ii = hom["z"], hom["s"], hom["r"], hom["i"]
    for t, val in enumerate(coeffs):
        if val == 0:
            continue
        num, den = val.numerator, val.denominator
        if den % p == 0:
            raise ZeroDivisionError("denominator vanishes mod p")
        ez = t % 6
        u = t // 6
        es = u % 2
        u //= 2
        er = u % 2
        ei = u // 2
        term = (num % p) * pow(den % p, -1, p) % p
        term = term * pow(z, ez, p) % p
        term = term * pow(s, es, p) % p
        term = term * pow(r, er, p) % p
        term = term * pow(ii, ei, p) % p
        acc = (acc + term) % p
    return acc


def reduce_vec(vec, hom, p):
    return [reduce_cyc(x, hom, p) for x in vec]


def orbit_of(group, pt, p):
    keys = {}
    for U, W in group["U_to_W"].items():
        im = apply_point(U, W, pt, p)
        if im[0] is None or im[1] is None:
            raise RuntimeError("vector collapsed")
        keys.setdefault(im, []).append(U)
    return keys


def stabilizer_symplectic(group, pt, p, z):
    """Return symplectic matrices of ordinary stabilizers, via conjugation."""
    U_to_W = group["U_to_W"]
    stab = []
    for U, W in U_to_W.items():
        im = apply_point(U, W, pt, p)
        if im == pt:
            # sigma from images of (1,0) and (0,1)
            cols = []
            for basis in ((1, 0), (0, 1)):
                M = conj_disp(U, W, basis[0], basis[1], z, p)
                lab = identify_p(M, z, p)
                if lab is None:
                    cols.append(None)
                else:
                    cols.append(lab)
            stab.append(cols)
    return stab


def conj_disp(U, W, p1, p2, z, p):
    Uinv = transpose_p(W)
    D = D_matrix_p(p1, p2, z, p)
    return matmul_p(Uinv, matmul_p(D, U, p), p)


def identify_p(M, z, p):
    shifts = set()
    entries = []
    positions = []
    for col in range(7):
        rows = [r for r in range(7) if M[r][col] % p]
        if len(rows) != 1:
            return None
        r = rows[0]
        shifts.add((r - col) % 7)
        entries.append(M[r][col] % p)
        positions.append(r)
    if len(shifts) != 1:
        return None
    p1 = next(iter(shifts))
    # match a scalar times D
    for p2 in range(7):
        phase = pow(z, (4 * p1 * p2) % 7, p)
        # chi * phase = entries[0]  (column 0, omega^0)
        if phase == 0:
            continue
        chi = entries[0] * pow(phase, -1, p) % p
        ok = True
        for col in range(7):
            pred = chi * phase * pow(z, (p2 * col) % 7, p) % p
            if M[(col + p1) % 7][col] % p != pred:
                ok = False
                break
        if ok:
            return (p1, p2, chi)
    return None


def sl_from_stab_cols(cols):
    if cols[0] is None or cols[1] is None:
        return None
    e1, e2 = cols[0], cols[1]
    # discard chi
    M = (e1[0], e2[0], e1[1], e2[1])
    det = (M[0] * M[3] - M[1] * M[2]) % 7
    tr = (M[0] + M[3]) % 7
    return {"matrix": M, "det": det, "trace": tr}


def wh_displacements(z, p):
    ops = []
    for a, b in itertools.product(range(7), repeat=2):
        U = D_matrix_p(a, b, z, p)
        # inverse transpose: invert then transpose. D^{-1} = D_{-a,-b} times a possible cocycle.
        # Compute inverse by linear algebra.
        Uinv = mat_inv(U, p)
        W = transpose_p(Uinv)
        Un, Wn = normalize_pair(U, W, p)
        ops.append((Un, Wn, (a, b)))
    return ops


def mat_inv(A, p):
    M = [list(row) + [1 if i == j else 0 for j in range(7)] for i, row in enumerate(A)]
    for col in range(7):
        piv = None
        for r in range(col, 7):
            if M[r][col] % p:
                piv = r
                break
        if piv is None:
            raise ZeroDivisionError("singular inv")
        M[col], M[piv] = M[piv], M[col]
        invp = pow(M[col][col], -1, p)
        M[col] = [(x * invp) % p for x in M[col]]
        for r in range(7):
            if r == col:
                continue
            f = M[r][col]
            if f:
                M[r] = [(M[r][c] - f * M[col][c]) % p for c in range(14)]
    return [row[7:] for row in M]


def enumerate_sl():
    out = []
    for a, b, c, d in itertools.product(range(7), repeat=4):
        if (a * d - b * c) % 7 == 1:
            out.append((a, b, c, d))
    return out


# ---------------------------------------------------------------------------
# Scott–Grassl algebraic fiducials inside the same tower
# ---------------------------------------------------------------------------


def sg_vectors(s, r, G):
    """Positive r1 = -i G / (s r), matching sqrt(1+2 sqrt(2)) in the standard embedding."""
    ii = Cyc.const(I_elem())
    # Standard embedding: -i G /(s r) = +sqrt(1+2 sqrt(2)).
    r1 = div_qsri_scalar((Cyc.const(0) - ii) * G, s * r)
    one = Cyc.const(1)
    # 7a
    a0 = ((-s + 2) * r1 + (s * 3 - 2)) * ii - s * r1 - s
    a1 = ((s + 2) * r1 + (s + 4)) * ii + (s - 2) * r1 - s
    four = Cyc.const(4)
    sga = [a0, a1, a1, four, a1, four, four]
    # 7b
    b0 = s * r1 * ii - s - 2
    two = Cyc.const(2)
    b3 = (Cyc.const(0) - r1) * ii + s - 1
    sgb = [b0, two, two, b3, two, b3, b3]
    return r1, sga, sgb


# ---------------------------------------------------------------------------
# Drivers
# ---------------------------------------------------------------------------


def unit_tests():
    s, r = S_elem(), R_elem()
    assert (s * s - 2).is_zero() if hasattr(s * s - 2, "is_zero") else s * s == QS(2)
    assert s * s == QS(2, 0)
    r2 = r * r
    assert r2 == QSR(QS(Fraction(-1, 2), 1), QS(0))
    ii = I_elem()
    assert (ii * ii) == QSRI(QSR(QS(-1), QS(0)), QSR(QS(0), QS(0)))
    z = Cyc.zeta(1)
    assert (z * z * z * z * z * z * z) == Cyc.const(1)
    # z^6 + z^5 + ... + 1 = 0
    acc = Cyc.const(1)
    w = Cyc.const(1)
    for _ in range(6):
        w = w * z
        acc = acc + w
    assert acc.is_zero()
    G = gauss_sum()
    assert (G * G + 7).is_zero()
    assert (G.conj() + G).is_zero()
    assert G.conj().conj() == G
    # random associativity / conjugation homomorphism, deterministic
    import random

    rng = random.Random(20261102)
    for _ in range(15):
        def rnd_qsri():
            def rnd_qs():
                return QS(rng.randint(-2, 2), rng.randint(-2, 2))
            return QSRI(QSR(rnd_qs(), rnd_qs()), QSR(rnd_qs(), rnd_qs()))

        def rnd_cyc():
            return Cyc(tuple(rnd_qsri() for _ in range(6)))

        a, b, c = rnd_cyc(), rnd_cyc(), rnd_cyc()
        assert (a * b) * c == a * (b * c)
        assert (a + b) * c == a * c + b * c
        assert (a * b).conj() == a.conj() * b.conj()
    # inverse of a small constant
    et = Cyc.const(1) + Cyc.const(I_elem()) * (Cyc.const(S_elem()) * 2 - 1)
    back = div_qsri_scalar(et, et)
    assert back == Cyc.const(1)
    return True


def all_seeds():
    s = Cyc.const(S_elem())
    r = Cyc.const(R_elem())
    G = gauss_sum()
    sm = -s
    rm = div_qsri_scalar(G, Cyc.const(QSR(QS(2), QS(0))) * r)
    assert (rm * rm - (sm - Cyc.const(Fraction(1, 2)))).is_zero()
    specs = {
        "F1": family1(s, r),
        "F2": family2(s, r),
        "G1": family1(sm, rm),
        "G2": family2(sm, rm),
    }
    return specs, s, r, G


def run_exact():
    t0 = time.time()
    assert unit_tests()
    specs, s, r, G = all_seeds()
    out = {"unit_tests": True, "seconds": None, "seeds": {}, "sg": {}, "covariance": None}
    P = permutation_zauner()
    for name, (x, y) in specs.items():
        rep = q_report(x, y)
        rep["quartic_bad"] = quartic_residuals(x, y)
        rep["doubling_symmetry"] = doubly_symmetric(x) and doubly_symmetric(y)
        rep["fixed_by_P"] = all(
            (mat_vec(P, x)[j] - x[j]).is_zero() and (mat_vec(P, y)[j] - y[j]).is_zero()
            for j in range(7)
        )
        # drop bulky
        rep["q_bad_count"] = len(rep.pop("q_bad"))
        rep["quartic_bad_count"] = len(rep.pop("quartic_bad"))
        out["seeds"][name] = rep
        print("exact", name, rep, flush=True)
    r1, sga, sgb = sg_vectors(s, r, G)
    out["sg"]["r1_sq_ok"] = (r1 * r1 - (s * 2 + 1)).is_zero()
    out["sg"]["r1_real"] = (r1.conj() - r1).is_zero()
    for label, phi in ("7a", sga), ("7b", sgb):
        b = [t.conj() for t in phi]
        rep = q_report(phi, b)
        rep["q_bad_count"] = len(rep.pop("q_bad"))
        rep["doubling_symmetry"] = doubly_symmetric(phi)
        rep["fixed_by_P"] = all((mat_vec(P, phi)[j] - phi[j]).is_zero() for j in range(7))
        # compare projectively to seeds, both (phi, conj) and the swap
        matches = []
        for name, (x, y) in specs.items():
            if parallel_vec(x, phi) and parallel_vec(y, b):
                matches.append(name + ":direct")
            if parallel_vec(x, b) and parallel_vec(y, phi):
                matches.append(name + ":swap")
        rep["seed_parallel"] = matches
        out["sg"][label] = rep
        print("sg", label, rep, flush=True)
    out["covariance"] = check_generator_covariance()
    print("covariance", out["covariance"], flush=True)
    # P symplectic image
    # U = P, W = P since P^{-T} = P for this permutation (P^T = P^{-1} and P^2 = P^{-1}? )
    # P: (Pv)_j = v_{4j}. Order 3, P^3 = I, P^{-1} = P^2.
    # P^T = P^{-1} = P^2, so P^{-T} = (P^T)^{-1} wait: P^{-T} = (P^{-1})^T = (P^2)^T.
    # Since P is real orthogonal? Permutation matrices satisfy P^T = P^{-1}, hence P^{-T} = P.
    # Check P * P^T = I and P^{-T}=P.
    Pt = transpose(P)
    out["P_orthogonal"] = mat_eq(mat_mul(P, Pt), eye_cyc())
    out["P_order"] = mat_eq(mat_mul(P, mat_mul(P, P)), eye_cyc()) and not mat_eq(P, eye_cyc())
    # covariance data for P itself
    WP = P  # claimed
    out["P_WT"] = mat_eq(mat_mul(P, transpose(WP)), eye_cyc())
    images = {}
    for p1, p2 in itertools.product(range(7), repeat=2):
        M = mat_mul(transpose(WP), mat_mul(D_matrix(p1, p2), P))
        images[(p1, p2)] = identify_displacement(M)
    bad = [k for k, v in images.items() if v is None]
    e1 = images.get((1, 0))
    e2 = images.get((0, 1))
    sl = None
    if e1 and e2:
        sl = [e1[0], e2[0], e1[1], e2[1]]
        det = (sl[0] * sl[3] - sl[1] * sl[2]) % 7
        tr = (sl[0] + sl[3]) % 7
    else:
        det = tr = None
    chi_ok = True
    for p1, p2 in images:
        if images[(p1, p2)] is None:
            continue
        chi = images[(p1, p2)][2]
        other = images.get(((-p1) % 7, (-p2) % 7))
        if other is None or not (chi * other[2] - 1).is_zero():
            chi_ok = False
    out["P_clifford"] = {
        "unidentified": bad,
        "sl": sl,
        "det": det,
        "trace": tr,
        "chi_pair_ok": chi_ok,
    }
    print("P", out["P_clifford"], "orth", out["P_orthogonal"], "order3", out["P_order"], flush=True)
    out["seconds"] = round(time.time() - t0, 3)
    # keep vectors for the finite-field stage
    return out, specs, (sga, sgb), P


def parallel_vec(u, v):
    for i in range(7):
        for j in range(7):
            if not (u[i] * v[j] - u[j] * v[i]).is_zero():
                return False
    if all(t.is_zero() for t in u) or all(t.is_zero() for t in v):
        return False
    return True


def sym_matrix_of(cols):
    if not cols or cols[0] is None or cols[1] is None:
        return None
    e1, e2 = cols[0], cols[1]
    return (e1[0] % 7, e2[0] % 7, e1[1] % 7, e2[1] % 7)


def run_prime(p, specs, sg_pair):
    t0 = time.time()
    hom = find_hom(p)
    if hom is None:
        return {"p": p, "error": "no hom"}
    print(f"hom p={p}", {k: hom[k] for k in ("s", "r", "i", "z")}, "roots", hom["quartic_roots"], flush=True)
    z = hom["z"]
    group = build_group(z, p)
    print(f"group order {group['order']} in {time.time()-t0:.1f}s", flush=True)
    # kernel / symplectic image, computed for every element would be slow;
    # check the 49 displacements sit in the group and are distinct, and
    # sigma of generators together with order.
    disps = wh_displacements(z, p)
    disp_keys = {}
    for Un, Wn, lab in disps:
        disp_keys.setdefault(Un, []).append(lab)
    in_group = sum(1 for Un in disp_keys if Un in group["U_to_W"])
    # sigma image of a transversal: compute sigma for every group element
    t1 = time.time()
    image_count = {}
    kernel = 0
    sigma_fail = 0
    chi_fail = 0
    not_linear = 0
    for U, W in group["U_to_W"].items():
        cols = []
        chis = {}
        ok = True
        labels = {}
        for basis in ((1, 0), (0, 1), (1, 1)):
            M = conj_disp(U, W, basis[0], basis[1], z, p)
            lab = identify_p(M, z, p)
            if lab is None:
                ok = False
                break
            labels[basis] = lab
        if not ok:
            sigma_fail += 1
            continue
        e1 = labels[(1, 0)]
        e2 = labels[(0, 1)]
        e11 = labels[(1, 1)]
        if ((e1[0] + e2[0]) % 7, (e1[1] + e2[1]) % 7) != (e11[0], e11[1]):
            not_linear += 1
        # chi(p) chi(-p) = 1 for the three tested, plus a full sweep is too much;
        # check the two basis vectors and their negatives.
        for basis in ((1, 0), (0, 1)):
            lab = labels[basis]
            Mn = conj_disp(U, W, (-basis[0]) % 7, (-basis[1]) % 7, z, p)
            labn = identify_p(Mn, z, p)
            if labn is None or (lab[2] * labn[2]) % p != 1:
                chi_fail += 1
                break
            if labn is not None and ((labn[0] + lab[0]) % 7 or (labn[1] + lab[1]) % 7):
                # sigma(-v) should be -sigma(v)
                chi_fail += 1
                break
        Msl = (e1[0], e2[0], e1[1], e2[1])
        det = (Msl[0] * Msl[3] - Msl[1] * Msl[2]) % 7
        if det != 1:
            not_linear += 1
        image_count[Msl] = image_count.get(Msl, 0) + 1
        if Msl == (1, 0, 0, 1):
            kernel += 1
    sl = enumerate_sl()
    missing_sl = [m for m in sl if m not in image_count]
    extra_sl = [m for m in image_count if m not in set(sl)]
    fibres = sorted(set(image_count.values()))
    print(
        f"sigma done {time.time()-t1:.1f}s kernel={kernel} fail={sigma_fail} "
        f"chi_fail={chi_fail} not_linear={not_linear} missingSL={len(missing_sl)} "
        f"fibres={fibres[:5]} nimage={len(image_count)}",
        flush=True,
    )
    # orbits of four seeds and of T(seeds)
    seed_pts = {}
    for name, (x, y) in specs.items():
        a = reduce_vec(x, hom, p)
        b = reduce_vec(y, hom, p)
        if all(t % p == 0 for t in a) or all(t % p == 0 for t in b):
            raise RuntimeError(f"{name} collapses mod {p}")
        seed_pts[name] = (norm_vec(a, p), norm_vec(b, p))
    sga, sgb = sg_pair
    sg_pts = {}
    for label, phi in ("7a", sga), ("7b", sgb):
        a = reduce_vec(phi, hom, p)
        b = reduce_vec([t.conj() for t in phi], hom, p)
        sg_pts[label] = (norm_vec(a, p), norm_vec(b, p))
        sg_pts[label + "swap"] = (norm_vec(b, p), norm_vec(a, p))

    orbit_info = {}
    membership = {k: [] for k in sg_pts}
    all_points = {}
    for name, pt in seed_pts.items():
        orb = orbit_of(group, pt, p)
        tpt = (pt[1], pt[0])
        torb = orbit_of(group, tpt, p)
        inter = set(orb) & set(torb)
        # stabilizer
        stabU = orb[pt]
        cols_list = []
        for U in stabU:
            W = group["U_to_W"][U]
            cols = []
            for basis in ((1, 0), (0, 1)):
                lab = identify_p(conj_disp(U, W, basis[0], basis[1], z, p), z, p)
                cols.append(lab)
            cols_list.append(sl_from_stab_cols(cols))
        # WH freeness on this point
        wh_images = set()
        for Un, Wn, lab in disps:
            wh_images.add(apply_point(Un, Wn, pt, p))
        info = {
            "orbit": len(orb),
            "T_orbit": len(torb),
            "T_in_orbit": tpt in orb,
            "intersection": len(inter),
            "stab": len(stabU),
            "stab_sl": cols_list,
            "wh_images": len(wh_images),
        }
        orbit_info[name] = info
        for q in orb:
            all_points.setdefault(q, []).append(name)
        for q in torb:
            all_points.setdefault(q, []).append("T" + name)
        for label, spt in sg_pts.items():
            if spt in orb:
                membership[label].append(name)
            if spt in torb:
                membership[label].append("T" + name)
        print(name, info, flush=True)
    # ordinary orbit partition: orbits of seeds and of T(seeds) if new
    ordinary = []
    seen_pts = set()
    reps = []
    for name, pt in list(seed_pts.items()):
        reps.append((name, pt))
        reps.append(("T" + name, (pt[1], pt[0])))
    for name, pt in reps:
        if pt in seen_pts:
            continue
        orb = set(orbit_of(group, pt, p))
        ordinary.append({"rep": name, "size": len(orb), "overlap_previous": len(orb & seen_pts)})
        seen_pts |= orb
    # distinct count
    distinct = len(all_points)
    # family extended sizes from the four seeds, disjoint union
    families = {}
    claimed_points = set()
    for name, pt in seed_pts.items():
        orb = set(orbit_of(group, pt, p))
        torb = set(orbit_of(group, (pt[1], pt[0]), p))
        fam = orb | torb
        families[name] = len(fam)
        claimed_points |= fam
    print(
        "distinct_labeled",
        distinct,
        "union",
        len(claimed_points),
        "ordinary",
        ordinary,
        "families",
        families,
        "sg",
        membership,
        flush=True,
    )
    return {
        "p": p,
        "hom": {k: hom[k] for k in ("s", "r", "i", "z", "quartic_roots")},
        "group_order": group["order"],
        "displacements_distinct": len(disp_keys),
        "displacements_in_group": in_group,
        "kernel": kernel,
        "sigma_fail": sigma_fail,
        "chi_fail": chi_fail,
        "not_linear": not_linear,
        "sl_missing": len(missing_sl),
        "sl_extra": len(extra_sl),
        "fibre_sizes": fibres,
        "n_symplectic_images": len(image_count),
        "seeds": orbit_info,
        "ordinary_orbits": ordinary,
        "extended_family_sizes": families,
        "union": len(claimed_points),
        "sg_membership": membership,
        "seconds": round(time.time() - t0, 3),
    }


def word_to_sg(p, specs, sg_pair, group, hom):
    """BFS a short word taking a seed point to an SG point. Replay is separate."""
    z = hom["z"]
    gens = generators_p(z, p)  # 8 generators, index aligned with build if rebuilt
    # Rebuild parent pointers on the POINT set, not on the group.
    # Use the already built group only to apply elements; BFS uses the 8 gens.
    sga, sgb = sg_pair
    targets = {}
    for label, phi in ("7a", sga), ("7b", sgb):
        a = norm_vec(reduce_vec(phi, hom, p), p)
        b = norm_vec(reduce_vec([t.conj() for t in phi], hom, p), p)
        targets[label] = (a, b)
        targets[label + "swap"] = (b, a)
    found = {}
    for name, (x, y) in specs.items():
        start = (norm_vec(reduce_vec(x, hom, p), p), norm_vec(reduce_vec(y, hom, p), p))
        parent = {start: None}
        how = {}
        dq = [start]
        qi = 0
        want = set(targets.values())
        hit = {}
        while qi < len(dq) and len(hit) < len(want):
            pt = dq[qi]
            qi += 1
            # ordinary generators
            for gi, (gname, U, W) in enumerate(gens):
                Un, Wn = normalize_pair(U, W, p)
                npt = apply_point(Un, Wn, pt, p)
                if npt not in parent:
                    parent[npt] = pt
                    how[npt] = ("G", gi, gname)
                    dq.append(npt)
                    if npt in want and npt not in hit:
                        hit[npt] = ("G", gi, gname)
            # one transpose
            tpt = (pt[1], pt[0])
            if tpt not in parent:
                parent[tpt] = pt
                how[tpt] = ("T", None, "T")
                dq.append(tpt)
        for label, spt in targets.items():
            if spt in parent:
                # recover word
                word = []
                cur = spt
                while parent[cur] is not None:
                    word.append(how[cur])
                    cur = parent[cur]
                word.reverse()
                found.setdefault(label, []).append({"seed": name, "length": len(word), "word": [(w[0], w[2]) for w in word]})
        print("bfs", name, "reached", len(parent), "hits", list(found), flush=True)
    return found


def replay_word(specs, sg_pair, word, seed_name, p_check=None):
    """Apply a word of ('G', name) or ('T',) steps in the exact tower."""
    x, y = specs[seed_name]
    x = list(x)
    y = list(y)
    gen = {n: (U, W) for n, U, W in generators_exact()}
    # inverses
    invs = {}
    for n, U, W in generators_exact():
        invs[n + "inv"] = (transpose(W), transpose(U))
    gen.update(invs)
    for kind, name in word:
        if kind == "T":
            x, y = y, x
        else:
            U, W = gen[name]
            x = mat_vec(U, x)
            y = mat_vec(W, y)
    return x, y


def main():
    exact, specs, sg_pair, P = run_exact()
    primes = {}
    for p in (673, 953):
        primes[str(p)] = run_prime(p, specs, sg_pair)
    # Lift one SG match per label through an exact word, searched mod 673.
    hom = find_hom(673)
    # The group inside run_prime was not returned. Search words with a fresh BFS
    # that stores only the word, using generators_p. 10976 points * 8 is fine.
    print("searching exact words", flush=True)
    word_hits = search_words(673, hom, specs, sg_pair)
    verified = []
    for label, hits in word_hits.items():
        if not hits:
            verified.append({"label": label, "ok": False, "reason": "no word"})
            continue
        hit = min(hits, key=lambda h: h["length"])
        # replay the shortest
        x, y = replay_word(specs, sg_pair, hit["word_full"], hit["seed"])
        phi = {"7a": sg_pair[0], "7b": sg_pair[1], "7aswap": [t.conj() for t in sg_pair[0]], "7bswap": [t.conj() for t in sg_pair[1]]}[label]
        # target pair
        if label.endswith("swap"):
            base = sg_pair[0] if label.startswith("7a") else sg_pair[1]
            target_a = [t.conj() for t in base]
            target_b = list(base)
        else:
            base = sg_pair[0] if label.startswith("7a") else sg_pair[1]
            target_a = list(base)
            target_b = [t.conj() for t in base]
        ok = parallel_vec(x, target_a) and parallel_vec(y, target_b)
        verified.append(
            {
                "label": label,
                "seed": hit["seed"],
                "length": hit["length"],
                "word": hit["word"],
                "exact_parallel": ok,
            }
        )
        print("replay", label, hit["seed"], hit["length"], ok, flush=True)
    result = {"exact": exact, "primes": primes, "sg_words": verified}

    def jsonify(obj):
        if isinstance(obj, tuple):
            return [jsonify(x) for x in obj]
        if isinstance(obj, dict):
            return {str(k): jsonify(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [jsonify(x) for x in obj]
        if isinstance(obj, Fraction):
            return str(obj)
        return obj

    path = "summary.json"
    with open(path, "w") as f:
        json.dump(jsonify(result), f, indent=2)
    print("wrote", path, flush=True)


def search_words(p, hom, specs, sg_pair):
    z = hom["z"]
    gens = []
    for name, U, W in generators_p(z, p):
        Un, Wn = normalize_pair(U, W, p)
        gens.append((name, Un, Wn))
    targets = {}
    for label, phi in ("7a", sg_pair[0]), ("7b", sg_pair[1]):
        a = norm_vec(reduce_vec(phi, hom, p), p)
        b = norm_vec(reduce_vec([t.conj() for t in phi], hom, p), p)
        targets[label] = (a, b)
        targets[label + "swap"] = (b, a)
    found = {k: [] for k in targets}
    for sname, (x, y) in specs.items():
        start = (norm_vec(reduce_vec(x, hom, p), p), norm_vec(reduce_vec(y, hom, p), p))
        parent = {start: None}
        how = {}
        dq = [start]
        qi = 0
        needed = set(targets.values())
        got = set()
        while qi < len(dq) and got != needed:
            pt = dq[qi]
            qi += 1
            cands = []
            for name, U, W in gens:
                cands.append((("G", name), apply_point(U, W, pt, p)))
            cands.append((("T", "T"), (pt[1], pt[0])))
            for step, npt in cands:
                if npt not in parent:
                    parent[npt] = pt
                    how[npt] = step
                    dq.append(npt)
                    if npt in needed:
                        got.add(npt)
        for label, spt in targets.items():
            if spt in parent:
                word_full = []
                cur = spt
                while parent[cur] is not None:
                    word_full.append(how[cur])
                    cur = parent[cur]
                word_full.reverse()
                found[label].append(
                    {
                        "seed": sname,
                        "length": len(word_full),
                        "word": word_full,
                        "word_full": word_full,
                    }
                )
        print(f"wordsearch {sname} reached {len(parent)}", flush=True)
    return found


if __name__ == "__main__":
    main()
