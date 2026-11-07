#!/usr/bin/env python3
"""Exact finite-field tools for the complexified equal-overlap fibre.

No third-party modules. Elements of GF(p^n) are integers with low-first
base-p coefficients. Projective points are (tuple(a), tuple(b)).
See ../GROUPS.md for the conventions, limitations and public API.
"""

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

from collections import Counter, deque
from math import gcd, isqrt, lcm
import argparse
import json
import platform
import random
import sys
import time


SEED = 20261031


def prime_factors(n):
    """Distinct positive prime factors, in increasing order."""
    out = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out


def divisors(n):
    return [r for r in range(1, n + 1) if n % r == 0]


def _trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def _prem(a, b, p):
    a = _trim(list(a))
    b = _trim(list(b))
    ib = pow(b[-1], -1, p)
    while len(a) >= len(b) and a != [0]:
        c = a[-1] * ib % p
        k = len(a) - len(b)
        for j, v in enumerate(b):
            a[j + k] = (a[j + k] - c * v) % p
        _trim(a)
    return a


def _pgcd(a, b, p):
    while b != [0]:
        a, b = b, _prem(a, b, p)
    v = pow(a[-1], -1, p)
    return [(v * c) % p for c in a]


def _pmul(a, b, modulus, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return _prem(c, modulus, p)


def _ppow(a, e, modulus, p):
    out = [1]
    while e:
        if e & 1:
            out = _pmul(out, a, modulus, p)
        a = _pmul(a, a, modulus, p)
        e //= 2
    return out


def is_irreducible(p, modulus):
    """Rabin's exact irreducibility criterion over the prime field."""
    f = _trim([int(c) % p for c in modulus])
    n = len(f) - 1
    if n < 1 or f[-1] != 1:
        return False
    x = _prem([0, 1], f, p)
    xp = x
    check = {n // r for r in prime_factors(n)}
    for k in range(1, n + 1):
        xp = _ppow(xp, p, f, p)
        if k in check:
            diff = [(xp[j] if j < len(xp) else 0)
                    - (x[j] if j < len(x) else 0)
                    for j in range(max(len(xp), len(x)))]
            if len(_pgcd(f, _trim([c % p for c in diff]), p)) > 1:
                return False
    return xp == x


def irreducible_polynomial(p, n):
    """First monic irreducible in low-coefficient integer order."""
    if n < 1:
        raise ValueError("extension degree must be positive")
    if n == 1:
        return (0, 1)
    for code in range(1, p ** n):
        if code % p == 0:
            continue
        v = code
        c = []
        for _ in range(n):
            c.append(v % p)
            v //= p
        c.append(1)
        if is_irreducible(p, c):
            return tuple(c)
    raise AssertionError("no irreducible polynomial found")


class GF:
    """GF(p)[x]/modulus, with integer low-coefficient encoding.

    ``modulus`` includes its monic leading coefficient. ``GF(5, [2,0,1])``
    has x^2=3, and its element x is the integer 5. Python integers passed to
    arithmetic methods are element codes. Use scalar(k) to embed an integer.
    """

    def __init__(self, p, modulus=(0, 1), *, check=True, tables=True):
        p = int(p)
        if p < 2 or any(p % r == 0 for r in range(2, isqrt(p) + 1)):
            raise ValueError("p must be prime")
        self.p = p
        self.modulus = tuple(int(c) % p for c in modulus)
        self.n = len(self.modulus) - 1
        if self.n < 1 or self.modulus[-1] != 1:
            raise ValueError("modulus must be monic of positive degree")
        if check and not is_irreducible(p, self.modulus):
            raise ValueError("modulus is reducible")
        self.q = p ** self.n
        self._weights = tuple(p ** k for k in range(self.n))
        self._digits = (tuple(self.coeffs(a) for a in range(self.q))
                        if self.q <= 65536 else None)
        self._negative = (tuple(self._raw_neg(a) for a in range(self.q))
                          if self.q <= 65536 else None)
        self._logs = None
        self._powers = None
        self.primitive = None
        if tables and self.q <= 65536:
            self._make_tables()

    def scalar(self, k):
        return int(k) % self.p

    def encode(self, coefficients):
        c = list(coefficients)
        if len(c) > self.n and any(c[self.n:]):
            raise ValueError("too many coefficients; reduce the polynomial first")
        return sum((int(x) % self.p) * self._weights[i]
                   for i, x in enumerate(c[:self.n]))

    def coeffs(self, a):
        if not isinstance(a, int) or not 0 <= a < self.q:
            raise ValueError("invalid finite-field element code")
        c = []
        for _ in range(self.n):
            c.append(a % self.p)
            a //= self.p
        return tuple(c)

    def _raw_neg(self, a):
        c = self._digits[a] if self._digits is not None else self.coeffs(a)
        return sum((-x % self.p) * w for x, w in zip(c, self._weights))

    def add(self, a, b):
        if self.n == 1:
            return (a + b) % self.p
        if self.p == 2:
            return a ^ b
        ac = self._digits[a] if self._digits is not None else self.coeffs(a)
        bc = self._digits[b] if self._digits is not None else self.coeffs(b)
        return sum(((x + y) % self.p) * w
                   for x, y, w in zip(ac, bc, self._weights))

    def neg(self, a):
        return self._negative[a] if self._negative is not None else self._raw_neg(a)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def _raw_mul(self, a, b):
        if not a or not b:
            return 0
        if self.n == 1:
            return a * b % self.p
        ac = self._digits[a] if self._digits is not None else self.coeffs(a)
        bc = self._digits[b] if self._digits is not None else self.coeffs(b)
        c = [0] * (2 * self.n - 1)
        for i, x in enumerate(ac):
            if x:
                for j, y in enumerate(bc):
                    c[i + j] += x * y
        for k in range(2 * self.n - 2, self.n - 1, -1):
            v = c[k] % self.p
            if v:
                for j in range(self.n):
                    c[k - self.n + j] -= v * self.modulus[j]
        return sum((c[i] % self.p) * self._weights[i] for i in range(self.n))

    def _raw_pow(self, a, e):
        out = 1
        while e:
            if e & 1:
                out = self._raw_mul(out, a)
            a = self._raw_mul(a, a)
            e //= 2
        return out

    def _make_tables(self):
        factors = prime_factors(self.q - 1)
        gen = next(a for a in range(1, self.q)
                   if all(self._raw_pow(a, (self.q - 1) // r) != 1
                          for r in factors))
        powers = []
        logs = [-1] * self.q
        v = 1
        for k in range(self.q - 1):
            if logs[v] != -1:
                raise ArithmeticError("multiplicative table repeated early")
            logs[v] = k
            powers.append(v)
            v = self._raw_mul(v, gen)
        if v != 1 or any(x < 0 for x in logs[1:]):
            raise ArithmeticError("multiplicative table is incomplete")
        self.primitive = gen
        self._logs = tuple(logs)
        self._powers = tuple(powers)

    def mul(self, a, b):
        if not a or not b:
            return 0
        if self._logs is not None:
            return self._powers[(self._logs[a] + self._logs[b]) % (self.q - 1)]
        return self._raw_mul(a, b)

    def pow(self, a, e):
        e = int(e)
        if not a:
            if e < 0:
                raise ZeroDivisionError("negative power of zero")
            return 1 if e == 0 else 0
        if self._logs is not None:
            return self._powers[(self._logs[a] * e) % (self.q - 1)]
        return self._raw_pow(a, e % (self.q - 1))

    def inv(self, a):
        if not a:
            raise ZeroDivisionError("inverse of zero")
        return self.pow(a, -1)

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    def sum(self, values):
        s = 0
        for v in values:
            s = self.add(s, v)
        return s

    def order(self, a):
        if not a:
            raise ValueError("zero has no multiplicative order")
        m = self.q - 1
        for r in prime_factors(m):
            while m % r == 0 and self.pow(a, m // r) == 1:
                m //= r
        return m

    def find_element_of_order(self, m):
        if m < 1 or (self.q - 1) % m:
            raise ValueError("requested order does not divide q-1")
        if self.primitive is not None:
            return self.pow(self.primitive, (self.q - 1) // m)
        factors = prime_factors(m)
        for a in range(1, self.q):
            z = self.pow(a, (self.q - 1) // m)
            if self.pow(z, m) == 1 and all(self.pow(z, m // r) != 1 for r in factors):
                return z
        raise AssertionError("element of requested order not found")

    def frobenius(self, a, power=1):
        return self.pow(a, self.p ** (int(power) % self.n))


def normalize_vector(field, vector):
    v = tuple(int(x) for x in vector)
    for x in v:
        if not 0 <= x < field.q:
            raise ValueError("invalid finite-field element code")
    try:
        first = next(x for x in v if x)
    except StopIteration:
        raise ValueError("a projective vector cannot be zero") from None
    z = field.inv(first)
    return tuple(field.mul(z, x) for x in v)


def normalize_point(field, point):
    a, b = point
    if len(a) != len(b) or len(a) < 2:
        raise ValueError("the two projective factors must have the same length >=2")
    return normalize_vector(field, a), normalize_vector(field, b)


def matrix_rank(field, rows, ncols=None, *, return_rref=False):
    """Exact Gaussian elimination. Empty matrices require ncols explicitly."""
    a = [list(row) for row in rows]
    ncols = len(a[0]) if ncols is None and a else (ncols or 0)
    if any(len(row) != ncols for row in a):
        raise ValueError("ragged matrix")
    rank = 0
    pivots = []
    for j in range(ncols):
        k = next((k for k in range(rank, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[rank], a[k] = a[k], a[rank]
        iv = field.inv(a[rank][j])
        a[rank] = [field.mul(iv, x) for x in a[rank]]
        for k in range(len(a)):
            if k != rank and a[k][j]:
                c = a[k][j]
                a[k] = [field.sub(x, field.mul(c, y))
                        for x, y in zip(a[k], a[rank])]
        pivots.append(j)
        rank += 1
        if rank == len(a):
            break
    if return_rref:
        return rank, tuple(pivots), tuple(tuple(row) for row in a)
    return rank


class Model:
    """ACFW displacement model, characteristic coprime to d.

    tau has exact order d for odd d, and 2d for even d. In both cases
    omega=tau^2 has exact order d. ACFW arXiv:1703.05981 (2)-(3).
    """

    def __init__(self, field, d, tau):
        self.field = field
        self.d = int(d)
        self.tau = int(tau)
        field.coeffs(self.tau)
        if self.d < 2 or gcd(field.p, self.d) != 1:
            raise ValueError("requires d>=2 and characteristic coprime to d")
        self.tau_order = self.d if self.d % 2 else 2 * self.d
        if field.order(self.tau) != self.tau_order:
            raise ValueError("tau has the wrong exact order for -exp(pi*i/d)")
        self.omega = field.mul(self.tau, self.tau)
        if field.order(self.omega) != self.d:
            raise ValueError("tau^2 must have order d")
        self.labels = tuple((r, s) for r in range(self.d) for s in range(self.d)
                            if r or s)
        self._displacements = {}
        self._group = None

    def normalize_point(self, point):
        point = normalize_point(self.field, point)
        if len(point[0]) != self.d:
            raise ValueError("wrong projective dimension")
        return point

    def _displacement(self, label):
        """(target row, coefficient) for each source column.

        Integer label representatives matter for D itself in even d.
        Always form the opposite label as (-r,-s), before reducing.
        """
        label = tuple(label)
        if label not in self._displacements:
            r, s = label
            phase = self.field.pow(self.tau, r * s)
            self._displacements[label] = tuple(
                ((j + r) % self.d,
                 self.field.mul(phase, self.field.pow(self.omega, s * j)))
                for j in range(self.d))
        return self._displacements[label]

    def displacement_action(self, label, vector):
        out = [0] * self.d
        for j, (i, c) in enumerate(self._displacement(label)):
            out[i] = self.field.mul(c, vector[j])
        return tuple(out)

    def overlap(self, point, label):
        a, b = point
        return self.field.sum(self.field.mul(self.field.mul(c, a[j]), b[i])
                              for j, (i, c) in enumerate(self._displacement(label)))

    def _overlap_gradient(self, point, label):
        a, b = point
        da = [0] * self.d
        db = [0] * self.d
        for j, (i, c) in enumerate(self._displacement(label)):
            da[j] = self.field.mul(c, b[i])
            db[i] = self.field.mul(c, a[j])
        return (self.field.sum(self.field.mul(a[j], da[j]) for j in range(self.d)),
                tuple(da + db))

    def jacobian_data(self, point, *, reference=(0, 1), with_matrix=False):
        """Equal-overlap and additional trace-zero Jacobian in a P x P chart.

        Eliminate t with K_ref=Z(ref)Z(-ref), then differentiate K_p-K_ref.
        rank_equal concerns the full possibly nonreduced fibre. rank_null
        additionally imposes Z(0)=0, so the two ranks are not interchangeable.
        """
        f = self.field
        point = self.normalize_point(point)
        a, b = point
        ia = next(i for i, x in enumerate(a) if x)
        ib = next(i for i, x in enumerate(b) if x)
        columns = [j for j in range(2 * self.d) if j not in (ia, self.d + ib)]
        reference = tuple(reference)
        if (reference[0] % self.d, reference[1] % self.d) == (0, 0):
            raise ValueError("reference overlap must be nonidentity")

        def product_gradient(p):
            z, dz = self._overlap_gradient(point, p)
            mz, mdz = self._overlap_gradient(point, (-p[0], -p[1]))
            return f.mul(z, mz), tuple(f.add(f.mul(mz, x), f.mul(z, y))
                                      for x, y in zip(dz, mdz))

        t, dt = product_gradient(reference)
        rows = []
        residuals = []
        for p in self.labels:
            kp, dkp = product_gradient(p)
            residuals.append(f.sub(kp, t))
            rows.append(tuple(f.sub(dkp[j], dt[j]) for j in columns))
        trace = f.sum(f.mul(x, y) for x, y in zip(a, b))
        trace_row = tuple((b + a)[j] for j in columns)
        rank_equal = matrix_rank(f, rows, len(columns))
        rank_null = matrix_rank(f, rows + [trace_row], len(columns))
        result = {
            "chart_a": ia, "chart_b": ib,
            "variables": tuple(("a", j) for j in range(self.d) if j != ia)
                         + tuple(("b", j) for j in range(self.d) if j != ib),
            "nvars": len(columns), "t": t, "trace": trace,
            "equal_overlap": not any(residuals),
            "t_nonzero": bool(t),
            "on_nullfiber": not trace and bool(t) and not any(residuals),
            "rank_equal": rank_equal, "rank_null": rank_null,
            "tangent_dim_equal": len(columns) - rank_equal,
            "tangent_dim_null": len(columns) - rank_null,
        }
        if with_matrix:
            result.update(rows_equal=tuple(rows), row_trace=trace_row,
                          residuals=tuple(residuals))
        return result

    def frobenius_point(self, point, power=1):
        point = self.normalize_point(point)
        return tuple(tuple(self.field.frobenius(x, power) for x in v)
                     for v in point)

    def frobenius_data(self, point):
        """Minimal coordinate field and Frobenius fixing tau, exactly."""
        f = self.field
        point = self.normalize_point(point)
        coefficient_degree = next(k for k in divisors(f.n)
                                  if f.frobenius(self.tau, k) == self.tau)
        absolute_degree = next(k for k in divisors(f.n)
                               if self.frobenius_point(point, k) == point)
        relative_degree = lcm(coefficient_degree, absolute_degree) // coefficient_degree
        orbit = []
        x = point
        for _ in range(relative_degree):
            orbit.append(x)
            x = self.frobenius_point(x, coefficient_degree)
        if x != point or len(set(orbit)) != relative_degree:
            raise ArithmeticError("Frobenius period verification failed")
        return {
            "coefficient_degree": coefficient_degree,
            "q0": f.p ** coefficient_degree,
            "absolute_coordinate_degree": absolute_degree,
            "absolute_coordinate_q": f.p ** absolute_degree,
            "relative_degree": relative_degree,
            "tau_inversion_exponents": tuple(k for k in range(f.n)
                                             if f.frobenius(self.tau, k) == f.inv(self.tau)),
            "orbit": tuple(orbit),
        }

    def frobenius_permutation(self, points, *, power=None):
        """Permutation of a supplied closed finite set, or an explicit error."""
        points = tuple(self.normalize_point(p) for p in points)
        index = {p: i for i, p in enumerate(points)}
        if len(index) != len(points):
            raise ValueError("input points are not distinct")
        if power is None:
            power = next(k for k in divisors(self.field.n)
                         if self.field.frobenius(self.tau, k) == self.tau)
        if self.field.frobenius(self.tau, power) != self.tau:
            raise ValueError("Frobenius does not fix the model coefficient tau")
        images = [self.frobenius_point(p, power) for p in points]
        missing = [p for p in images if p not in index]
        if missing:
            raise ValueError(f"input is not Frobenius closed: {len(missing)} images missing")
        return tuple(index[p] for p in images)

    def generators(self):
        """Ordinary projective Clifford generators F,S,X,Z, as matrix pairs.

        F_rs=omega^(r*s), S_jj=tau^(j*j). The second matrix is proportional
        to the inverse transpose of the first. Fourier's 1/d is omitted.
        """
        if not hasattr(self, "_generators"):
            f, d = self.field, self.d
            ident_label = (1, 0, 0, 1)
            fourier = tuple(f.pow(self.omega, r * s) for r in range(d) for s in range(d))
            invfourier = tuple(f.pow(self.omega, -r * s) for r in range(d) for s in range(d))
            shear = diagonal_matrix(tuple(f.pow(self.tau, j * j) for j in range(d)))
            invshear = diagonal_matrix(tuple(f.pow(self.tau, -j * j) for j in range(d)))
            shift = tuple(int(r == (s + 1) % d) for r in range(d) for s in range(d))
            clock = diagonal_matrix(tuple(f.pow(self.omega, j) for j in range(d)))
            invclock = diagonal_matrix(tuple(f.pow(self.omega, -j) for j in range(d)))
            data = (
                ("F", fourier, invfourier, (0, (-1) % d, 1, 0)),
                ("S", shear, invshear, (1, 0, 1, 1)),
                ("X", shift, shift, ident_label),
                ("Z", clock, invclock, ident_label),
            )
            self._generators = tuple(Action(self, u, v, label=label, name=name)
                                     for name, u, v, label in data)
        return self._generators

    def swap_action(self):
        """Algebraic extension of physical complex conjugation: (a,b)->(b,a).

        This is a linear involution of the complexified P x P scheme. It
        conjugates (U,U^-T) to (U^-T,U), corresponding on the cyclotomic
        generator matrices to tau->tau^-1. It is not arbitrary Frobenius.
        """
        ident = identity_matrix(self.d)
        return Action(self, ident, ident, swap=True,
                      label=(1, 0, 0, (-1) % self.d), name="J")

    def clifford_group(self, *, max_order=100000):
        if self._group is None:
            self._group = CliffordGroup(self, max_order=max_order)
        return self._group

    def orbit_with_transporters(self, point, *, extended=False, wh_only=False,
                                max_points=100000):
        """Generator BFS on points, without constructing the matrix group.

        Word entries are generator names in their application order. This
        returns actual transporters, and provides the orbit side of a
        Schreier-stabilizer computation without full-matrix BFS.
        """
        point = self.normalize_point(point)
        generators = self.generators()[2:] if wh_only else self.generators()
        if extended:
            generators += (self.swap_action(),)
        points = [point]
        parents = [None]
        edges = [None]
        index = {point: 0}
        queue = deque([0])
        while queue:
            k = queue.popleft()
            for g in generators:
                p = g.apply(points[k])
                if p not in index:
                    if len(points) >= max_points:
                        raise RuntimeError("point BFS exceeded max_points")
                    index[p] = len(points)
                    queue.append(len(points))
                    points.append(p)
                    parents.append(k)
                    edges.append(g.name)
        words = []
        for k in range(len(points)):
            w = []
            while parents[k] is not None:
                w.append(edges[k])
                k = parents[k]
            words.append(tuple(reversed(w)))
        return {"points": tuple(points), "words": tuple(words),
                "parents": tuple(parents), "edges": tuple(edges)}

    def orbit(self, point, *, extended=False, wh_only=False, max_points=100000):
        return self.orbit_with_transporters(point, extended=extended,
                                            wh_only=wh_only,
                                            max_points=max_points)["points"]

    def close_points(self, points, *, extended=False, max_points=100000):
        """Generator closure of supplied seeds, without a fibre-coverage claim."""
        points = list(dict.fromkeys(self.normalize_point(p) for p in points))
        known = set(points)
        generators = self.generators() + ((self.swap_action(),) if extended else ())
        queue = deque(points)
        while queue:
            point = queue.popleft()
            for g in generators:
                image = g.apply(point)
                if image not in known:
                    if len(points) >= max_points:
                        raise RuntimeError("seed closure exceeded max_points")
                    known.add(image)
                    points.append(image)
                    queue.append(image)
        return tuple(points)

    def wh_orbit(self, point):
        return self.orbit(point, wh_only=True, max_points=self.d * self.d + 1)

    def orbit_partition(self, points, *, extended=False, wh_only=False):
        """Partition a supplied generator-closed set, preserving input indices."""
        points = tuple(self.normalize_point(p) for p in points)
        index = {p: i for i, p in enumerate(points)}
        if len(index) != len(points):
            raise ValueError("input points are not distinct")
        generators = self.generators()[2:] if wh_only else self.generators()
        if extended:
            generators += (self.swap_action(),)
        unseen = set(range(len(points)))
        components = []
        while unseen:
            k = min(unseen)
            component = [k]
            unseen.remove(k)
            queue = deque([k])
            while queue:
                k = queue.popleft()
                for g in generators:
                    image = g.apply(points[k])
                    if image not in index:
                        raise ValueError(f"input is not {g.name}-closed; image of index {k} missing")
                    j = index[image]
                    if j in unseen:
                        unseen.remove(j)
                        component.append(j)
                        queue.append(j)
            components.append(tuple(sorted(component)))
        return tuple(components)


def identity_matrix(d):
    return tuple(int(i == j) for i in range(d) for j in range(d))


def diagonal_matrix(diagonal):
    d = len(diagonal)
    return tuple(diagonal[i] if i == j else 0 for i in range(d) for j in range(d))


def transpose_matrix(a, d):
    return tuple(a[j * d + i] for i in range(d) for j in range(d))


def projective_matrix(field, a):
    first = next((v for v in a if v), None)
    if first is None:
        raise ValueError("zero projective matrix")
    v = field.inv(first)
    return tuple(field.mul(v, x) for x in a)


def matrix_mul(field, a, b, d):
    out = [0] * (d * d)
    for i in range(d):
        for k in range(d):
            x = a[i * d + k]
            if x:
                for j in range(d):
                    y = b[k * d + j]
                    if y:
                        pos = i * d + j
                        out[pos] = field.add(out[pos], field.mul(x, y))
    return tuple(out)


def matrix_vector(field, a, v, d):
    return tuple(field.sum(field.mul(a[i * d + j], v[j]) for j in range(d))
                 for i in range(d))


def label_mul(a, b, d):
    return ((a[0] * b[0] + a[1] * b[2]) % d,
            (a[0] * b[1] + a[1] * b[3]) % d,
            (a[2] * b[0] + a[3] * b[2]) % d,
            (a[2] * b[1] + a[3] * b[3]) % d)


class Action:
    """Projective pair (U,V), with V proportional to U^-T, optionally swap.

    Matrices are flattened row-major. ``self.compose(h)`` means self after h.
    ``label`` is its symplectic/antisymplectic image modulo d only. In even d
    it deliberately does not claim to encode the full modulo-2d phase lift.
    """

    __slots__ = ("model", "U", "V", "swap", "label", "name")

    def __init__(self, model, u, v, *, swap=False, label=(1, 0, 0, 1), name=""):
        self.model = model
        self.U = projective_matrix(model.field, u)
        self.V = projective_matrix(model.field, v)
        self.swap = bool(swap)
        self.label = tuple(x % model.d for x in label)
        self.name = name

    @property
    def key(self):
        return self.U, self.swap

    def apply(self, point):
        a, b = point
        if self.swap:
            a, b = b, a
        f, d = self.model.field, self.model.d
        return normalize_vector(f, matrix_vector(f, self.U, a, d)), \
               normalize_vector(f, matrix_vector(f, self.V, b, d))

    def compose(self, other):
        if self.model is not other.model:
            raise ValueError("actions belong to different Model objects")
        f, d = self.model.field, self.model.d
        a, b = (other.V, other.U) if self.swap else (other.U, other.V)
        return Action(self.model, matrix_mul(f, self.U, a, d),
                      matrix_mul(f, self.V, b, d), swap=self.swap ^ other.swap,
                      label=label_mul(self.label, other.label, d))

    def inverse(self):
        d = self.model.d
        u, v = transpose_matrix(self.V, d), transpose_matrix(self.U, d)
        if self.swap:
            u, v = v, u
        a, b, c, e = self.label
        det = (a * e - b * c) % d
        iv = pow(det, -1, d)
        label = tuple(iv * x % d for x in (e, -b, -c, a))
        return Action(self.model, u, v, swap=self.swap, label=label)

    def power(self, exponent):
        if exponent < 0:
            return self.inverse().power(-exponent)
        ident = identity_matrix(self.model.d)
        out = Action(self.model, ident, ident)
        a = self
        while exponent:
            if exponent & 1:
                out = a.compose(out)
            a = a.compose(a)
            exponent //= 2
        return out

    def is_identity(self):
        return not self.swap and self.U == identity_matrix(self.model.d)

    def projective_order(self, group_order):
        if not self.power(group_order).is_identity():
            raise ValueError("supplied group_order does not annihilate this action")
        m = group_order
        for r in prime_factors(m):
            while m % r == 0 and self.power(m // r).is_identity():
                m //= r
        return m


def expected_clifford_order(d):
    """d^2 |SL(2,Z/dZ)|, used only as an independent comparison value."""
    sl_order = d ** 3
    for p in prime_factors(d):
        sl_order = sl_order // (p * p) * (p * p - 1)
    return d * d * sl_order


class CliffordGroup:
    """Projective matrix-pair BFS generated by F,S,X,Z.

    Matrices, not a prescribed order, decide when BFS stops. The computed
    order is then compared with d^2|SL2(Z/dZ)|. Extended elements are stored
    as an ordinary index plus one swap bit, without a second matrix BFS.
    """

    def __init__(self, model, *, max_order=100000):
        self.model = model
        self.generators = model.generators()
        ident = identity_matrix(model.d)
        self.elements = [Action(model, ident, ident)]
        self.parents = [None]
        self.edges = [None]
        self.index = {self.elements[0].U: 0}
        queue = deque([0])
        f, d = model.field, model.d
        while queue:
            k = queue.popleft()
            h = self.elements[k]
            for j, g in enumerate(self.generators):
                u = projective_matrix(f, matrix_mul(f, g.U, h.U, d))
                if u in self.index:
                    if self.elements[self.index[u]].label != label_mul(g.label, h.label, d):
                        raise ArithmeticError("projective collision has inconsistent label image")
                    continue
                if len(self.elements) >= max_order:
                    raise RuntimeError("matrix BFS exceeded max_order")
                v = matrix_mul(f, g.V, h.V, d)
                gnew = Action(model, u, v, label=label_mul(g.label, h.label, d))
                self.index[u] = len(self.elements)
                queue.append(len(self.elements))
                self.elements.append(gnew)
                self.parents.append(k)
                self.edges.append(j)
        self.order = len(self.elements)
        self.extended_order = 2 * self.order
        self.expected_order = expected_clifford_order(d)
        self.order_matches_expected = self.order == self.expected_order
        self._orders = {}

    def __len__(self):
        return self.order

    def action(self, index, *, swap=False):
        h = self.elements[index]
        if not swap:
            return h
        return Action(self.model, h.U, h.V, swap=True,
                      label=label_mul(h.label, (1, 0, 0, -1), self.model.d))

    def word(self, index, *, swap=False):
        word = []
        while self.parents[index] is not None:
            word.append(self.generators[self.edges[index]].name)
            index = self.parents[index]
        word.reverse()
        return (("J",) if swap else ()) + tuple(word)

    def element_order(self, index, *, swap=False):
        key = index, bool(swap)
        if key not in self._orders:
            self._orders[key] = self.action(index, swap=swap).projective_order(
                self.extended_order if swap else self.order)
        return self._orders[key]

    def stabilizer(self, point, *, extended=False, with_orders=True):
        point = self.model.normalize_point(point)
        fixed = []
        for swap in ((False, True) if extended else (False,)):
            for index in range(self.order):
                g = self.action(index, swap=swap)
                if g.apply(point) == point:
                    row = {"index": index, "swap": swap, "label_mod_d": g.label,
                           "trace_mod_d": (g.label[0] + g.label[3]) % self.model.d}
                    if with_orders:
                        row["projective_order"] = self.element_order(index, swap=swap)
                    fixed.append(row)
        return tuple(fixed)

    def stabilizer_data(self, point, *, extended=True, with_orders=True):
        fixed = self.stabilizer(point, extended=extended, with_orders=with_orders)
        ordinary_size = sum(not r["swap"] for r in fixed)
        if self.order % ordinary_size:
            raise ArithmeticError("ordinary orbit-stabilizer divisibility failed")
        result = {"ordinary_group_order": self.order,
                  "ordinary_stabilizer_order": ordinary_size,
                  "ordinary_orbit_size": self.order // ordinary_size,
                  "elements": fixed}
        if extended:
            if self.extended_order % len(fixed):
                raise ArithmeticError("extended orbit-stabilizer divisibility failed")
            result.update(extended_group_order=self.extended_order,
                          extended_stabilizer_order=len(fixed),
                          extended_orbit_size=self.extended_order // len(fixed))
        return result

    def verify(self, *, all_pairs=True):
        """Exact inverse-dual checks and BFS edge closure, no order oracle."""
        f, d = self.model.field, self.model.d
        ident = identity_matrix(d)
        for g in self.elements if all_pairs else self.generators:
            uv = projective_matrix(f, matrix_mul(f, g.U, transpose_matrix(g.V, d), d))
            if uv != ident:
                raise ArithmeticError("stored matrix pair is not inverse transpose")
        for g in self.generators:
            if g.V not in self.index:
                raise ArithmeticError("swap does not normalize the matrix group")
            for h in self.elements:
                u = projective_matrix(f, matrix_mul(f, g.U, h.U, d))
                if u not in self.index:
                    raise ArithmeticError("BFS output is not generator-closed")
        return {"order": self.order, "expected_order": self.expected_order,
                "order_matches_expected": self.order_matches_expected,
                "inverse_dual_checked": self.order if all_pairs else len(self.generators),
                "closure_edges_checked": self.order * len(self.generators),
                "swap_normalizer_generators_checked": len(self.generators)}

    def embed_into(self, target_model, embedding):
        """Faithfully re-encode a computed group in an extension field.

        ``embedding[a]`` is the target code of a source field element. The
        caller supplies a certified polynomial-root field embedding.
        """
        if self.model.d != target_model.d or embedding[self.model.tau] != target_model.tau:
            raise ValueError("field embedding does not match the target model")
        for g, h in zip(self.generators, target_model.generators()):
            if tuple(embedding[x] for x in g.U) != h.U or tuple(embedding[x] for x in g.V) != h.V:
                raise ArithmeticError("field embedding changes a Clifford generator")
        out = object.__new__(CliffordGroup)
        out.model = target_model
        out.generators = target_model.generators()
        out.elements = [Action(target_model, tuple(embedding[x] for x in g.U),
                              tuple(embedding[x] for x in g.V), label=g.label)
                        for g in self.elements]
        out.parents = list(self.parents)
        out.edges = list(self.edges)
        out.index = {g.U: i for i, g in enumerate(out.elements)}
        if len(out.index) != self.order:
            raise ArithmeticError("field embedding merged projective matrices")
        out.order = self.order
        out.extended_order = self.extended_order
        out.expected_order = self.expected_order
        out.order_matches_expected = self.order_matches_expected
        out._orders = dict(self._orders)
        out.construction = {"kind": "faithful_field_embedding", "source_q": self.model.field.q,
                            "source_modulus": self.model.field.modulus,
                            "source_tau": self.model.tau, "source_matrix_BFS_order": self.order}
        target_model._group = out
        return out


def field_embedding(source, target):
    """An exact explicit embedding found from a root of source.modulus.

    Returns (table, root). The fields must share their prime characteristic
    and have compatible degrees. Deterministic root search is suitable for
    the small fields in this exploration, not asymptotic field algorithms.
    """
    if source.p != target.p or target.n % source.n:
        raise ValueError("incompatible finite fields")

    def evaluate(coefficients, root):
        value = 0
        for coefficient in reversed(coefficients):
            value = target.add(target.mul(value, root), target.scalar(coefficient))
        return value

    root = next((a for a in range(target.q) if evaluate(source.modulus, a) == 0), None)
    if root is None:
        raise ArithmeticError("source modulus has no root in target")
    table = tuple(evaluate(source.coeffs(a), root) for a in range(source.q))
    if len(set(table)) != source.q or table[0] != 0 or table[1] != 1:
        raise ArithmeticError("polynomial-root embedding is not injective")
    return table, root


def reduce_model_to_coordinate_subfield(model, points):
    """Descend tau and all normalized coordinates to their common small field."""
    f = model.field
    points = tuple(model.normalize_point(p) for p in points)
    values = {model.tau}
    for point in points:
        for vector in point:
            values.update(vector)
    degree = next(k for k in divisors(f.n)
                  if all(f.frobenius(a, k) == a for a in values))
    if degree == f.n:
        return model, points, tuple(range(f.q)), {
            "used": False, "ambient_degree": f.n, "coordinate_and_tau_degree": degree}
    small = GF(f.p, irreducible_polynomial(f.p, degree))
    embedding, root = field_embedding(small, f)
    reverse = {a: i for i, a in enumerate(embedding)}
    if any(a not in reverse for a in values):
        raise ArithmeticError("minimal coordinate field and chosen embedding disagree")
    small_model = Model(small, model.d, reverse[model.tau])
    small_points = tuple(tuple(tuple(reverse[a] for a in vector) for vector in point)
                         for point in points)
    return small_model, small_points, embedding, {
        "used": True, "ambient_degree": f.n, "coordinate_and_tau_degree": degree,
        "small_q": small.q, "small_modulus": small.modulus, "small_tau": small_model.tau,
        "root_in_ambient": root, "embedding_table": embedding,
        "proof": "source modulus irreducible, root evaluated to zero, and all source codes map injectively",
    }


def _action_record(group, index, swap=False):
    action = group.action(index, swap=swap)
    return {"index": index, "swap": bool(swap), "U": action.U, "V": action.V,
            "label_mod_d": action.label,
            "trace_mod_d": (action.label[0] + action.label[3]) % group.model.d,
            "projective_order": group.element_order(index, swap=swap),
            "word": group.word(index, swap=swap)}


def stabilizer_certificate(model, points, *, source="", check_matrices=True):
    """Complete fixed-element certificates using one scan per ordinary orbit.

    Each point receives a transporter word. Its full stabilizer is obtained
    by conjugating the explicitly scanned representative stabilizer. Every
    resulting fixed action is checked at its target point. This never scans
    all group elements separately at every point.
    """
    points = tuple(model.normalize_point(p) for p in points)
    index = {p: i for i, p in enumerate(points)}
    if len(index) != len(points):
        raise ValueError("certificate input points must be distinct")
    group = model.clifford_group()
    matrix_check = group.verify() if check_matrices else None
    components = model.orbit_partition(points)
    extended_components = model.orbit_partition(points, extended=True)
    orbits = []
    point_records = [None] * len(points)
    fixed_actions_checked = 0
    representative_actions_scanned = 0
    for orbit_id, component in enumerate(components):
        representative = min(component)
        point = points[representative]
        fixed = group.stabilizer(point, extended=True, with_orders=True)
        representative_actions_scanned += group.extended_order
        ordinary_size = sum(not h["swap"] for h in fixed)
        if len(component) * ordinary_size != group.order:
            raise ArithmeticError("representative orbit-stabilizer mismatch")
        fixed_records = tuple(_action_record(group, h["index"], h["swap"]) for h in fixed)
        transported = {}
        for k, g in enumerate(group.elements):
            image = g.apply(point)
            if image not in index:
                raise ArithmeticError("supplied points do not contain the complete orbit")
            transported.setdefault(index[image], k)
        if set(transported) != set(component):
            raise ArithmeticError("transporter enumeration and point BFS disagree")
        order_counts = Counter(h["projective_order"] for h in fixed)
        ordinary_counts = Counter(h["projective_order"] for h in fixed if not h["swap"])
        ext_cyclic = any(h["projective_order"] == len(fixed) for h in fixed)
        ordinary_cyclic = any(h["projective_order"] == ordinary_size
                              for h in fixed if not h["swap"])
        orbits.append({
            "id": orbit_id, "representative_point_id": representative,
            "member_ids": component, "ordinary_orbit_size": len(component),
            "ordinary_stabilizer_order": ordinary_size,
            "extended_stabilizer_order": len(fixed),
            "extended_orbit_size": group.extended_order // len(fixed),
            "ordinary_stabilizer_is_cyclic": ordinary_cyclic,
            "extended_stabilizer_is_cyclic": ext_cyclic,
            "ordinary_stabilizer_order_counts": dict(sorted(ordinary_counts.items())),
            "extended_stabilizer_order_counts": dict(sorted(order_counts.items())),
            "representative_stabilizer": fixed_records,
        })
        for point_id in component:
            transporter_id = transported[point_id]
            trans = group.elements[transporter_id]
            itrans = trans.inverse()
            fixed_here = []
            keys = set()
            for h in fixed:
                action = trans.compose(group.action(h["index"], swap=h["swap"])).compose(itrans)
                if action.U not in group.index:
                    raise ArithmeticError("conjugate escaped the ordinary group coset")
                action_id = group.index[action.U]
                exact = group.action(action_id, swap=action.swap)
                if exact.V != action.V or exact.label != action.label:
                    raise ArithmeticError("conjugated matrix pair or label mismatch")
                if exact.apply(points[point_id]) != points[point_id]:
                    raise ArithmeticError("conjugated stabilizer does not fix the target")
                fixed_actions_checked += 1
                key = action_id, action.swap
                if key in keys:
                    raise ArithmeticError("stabilizer conjugation merged elements")
                keys.add(key)
                fixed_here.append({"index": action_id, "swap": action.swap,
                                   "label_mod_d": exact.label,
                                   "trace_mod_d": (exact.label[0] + exact.label[3]) % model.d,
                                   "projective_order": h["projective_order"],
                                   "conjugate_of": h["index"]})
            point_records[point_id] = {
                "id": point_id, "point": points[point_id], "ordinary_orbit_id": orbit_id,
                "transporter_index": transporter_id,
                "transporter_word": group.word(transporter_id),
                "stabilizer": tuple(fixed_here),
            }
    return {
        "format": "nf-stabilizer-certificate-v1", "seed": SEED,
        "python": platform.python_version(), "arithmetic": "exact finite field",
        "d": model.d, "p": model.field.p, "q": model.field.q,
        "modulus": model.field.modulus, "tau": model.tau, "omega": model.omega,
        "source": source, "point_count": len(points),
        "ordinary_group_order": group.order, "extended_group_order": group.extended_order,
        "group_order_comparison": {"formula_value": group.expected_order,
                                   "agrees": group.order_matches_expected},
        "group_matrix_checks": matrix_check,
        "group_construction": getattr(group, "construction", {"kind": "matrix_pair_BFS"}),
        "generators": tuple({"name": g.name, "U": g.U, "V": g.V,
                             "label_mod_d": g.label} for g in model.generators()),
        "swap_generator": {"name": "J", "definition": "(a,b)->(b,a)",
                           "is_field_frobenius": False},
        "word_convention": "generator names listed in application order; transporter*h*transporter^-1 fixes its target",
        "group_bfs": tuple({"parent": p, "generator": None if j is None else group.generators[j].name}
                           for p, j in zip(group.parents, group.edges)),
        "ordinary_orbits": tuple(orbits), "extended_orbits": extended_components,
        "representative_actions_scanned": representative_actions_scanned,
        "transported_fixed_actions_checked": fixed_actions_checked,
        "per_point": tuple(point_records),
        "completeness_boundary": "All stabilizers complete on the supplied generator-closed point set; polynomial-fibre completeness remains the responsibility of the point-source certificate.",
    }


def verify_stabilizer_certificate(data):
    """Rebuild from generator words and verify every transported fixed action."""
    f = GF(data["p"], data["modulus"])
    model = Model(f, data["d"], data["tau"])
    group = model.clifford_group()
    if group.order != data["ordinary_group_order"]:
        raise ArithmeticError("certificate group order mismatch")
    generators = {g.name: g for g in model.generators()}
    generators["J"] = model.swap_action()

    def read_word(word):
        out = group.elements[0]
        for name in word:
            out = generators[name].compose(out)
        return out

    records = data["per_point"]
    points = tuple(model.normalize_point(row["point"]) for row in records)
    if len(points) != data["point_count"] or len(set(points)) != len(points):
        raise ArithmeticError("certificate point count or uniqueness mismatch")
    if model.orbit_partition(points) != tuple(tuple(o["member_ids"]) for o in data["ordinary_orbits"]):
        raise ArithmeticError("certificate ordinary orbit partition mismatch")
    if model.orbit_partition(points, extended=True) != tuple(tuple(o) for o in data["extended_orbits"]):
        raise ArithmeticError("certificate extended orbit partition mismatch")
    representatives = {}
    checked = 0
    for orbit in data["ordinary_orbits"]:
        rep_id = orbit["representative_point_id"]
        expected = {(h["index"], h["swap"]) for h in group.stabilizer(points[rep_id], extended=True)}
        read = []
        for h in orbit["representative_stabilizer"]:
            action = read_word(h["word"])
            if action.U != tuple(h["U"]) or action.V != tuple(h["V"]) or action.swap != h["swap"]:
                raise ArithmeticError("representative word and stored matrices disagree")
            if group.index[action.U] != h["index"] or action.label != tuple(h["label_mod_d"]):
                raise ArithmeticError("representative action index or label mismatch")
            if action.apply(points[rep_id]) != points[rep_id]:
                raise ArithmeticError("representative action does not fix its point")
            if group.element_order(h["index"], swap=h["swap"]) != h["projective_order"]:
                raise ArithmeticError("representative action order mismatch")
            read.append(action)
        if expected != {(h["index"], h["swap"]) for h in orbit["representative_stabilizer"]}:
            raise ArithmeticError("representative stabilizer is incomplete")
        representatives[orbit["id"]] = (rep_id, tuple(zip(read, orbit["representative_stabilizer"])))
    for row in records:
        point = points[row["id"]]
        rep_id, fixed = representatives[row["ordinary_orbit_id"]]
        trans = read_word(row["transporter_word"])
        if trans.apply(points[rep_id]) != point:
            raise ArithmeticError("transporter word reaches the wrong point")
        computed = {}
        for h, representative_record in fixed:
            action = trans.compose(h).compose(trans.inverse())
            key = group.index[action.U], action.swap
            computed[key] = (action, representative_record)
            if action.apply(point) != point:
                raise ArithmeticError("transported action fails to fix its point")
            checked += 1
        if set(computed) != {(h["index"], h["swap"]) for h in row["stabilizer"]}:
            raise ArithmeticError("per-point stabilizer indices disagree")
        if len(row["stabilizer"]) != len(computed):
            raise ArithmeticError("per-point stabilizer repeats an element")
        for h in row["stabilizer"]:
            action, representative_record = computed[h["index"], h["swap"]]
            if (h["projective_order"] != representative_record["projective_order"]
                    or tuple(h["label_mod_d"]) != action.label
                    or h["trace_mod_d"] != (action.label[0] + action.label[3]) % model.d
                    or h["conjugate_of"] != representative_record["index"]):
                raise ArithmeticError("per-point stabilizer metadata mismatch")
    return {"verified": True, "points": len(points), "ordinary_group_order": group.order,
            "ordinary_orbits": len(representatives), "fixed_actions_checked": checked}


def _check_directional_jacobian(model, point, rng):
    """Independent first-coefficient check using direct bilinear overlaps."""
    f, d = model.field, model.d
    point = model.normalize_point(point)
    a, b = point
    data = model.jacobian_data(point, with_matrix=True)
    ha = [rng.randrange(f.q) for _ in range(d)]
    hb = [rng.randrange(f.q) for _ in range(d)]
    ha[data["chart_a"]] = 0
    hb[data["chart_b"]] = 0
    direction = tuple(ha[j] if factor == "a" else hb[j] for factor, j in data["variables"])

    def overlap_derivative(p):
        return f.add(model.overlap((ha, b), p), model.overlap((a, hb), p))

    def product_derivative(p):
        minus = -p[0], -p[1]
        return f.add(f.mul(overlap_derivative(p), model.overlap(point, minus)),
                     f.mul(model.overlap(point, p), overlap_derivative(minus)))

    dr = product_derivative((0, 1))
    for p, row in zip(model.labels, data["rows_equal"]):
        analytic = f.sum(f.mul(x, y) for x, y in zip(row, direction))
        if analytic != f.sub(product_derivative(p), dr):
            raise ArithmeticError("Jacobian directional coefficient mismatch")
    return len(model.labels)


def extract_points(data):
    """Read the coordinator's full-point or eigen-slice JSON formats."""
    if "per_point" in data:
        return [row["point"] for row in data["per_point"]]
    if "points" in data:
        return [row["point"] if isinstance(row, dict) else row for row in data["points"]]
    if "rows" in data:
        return [point["point"] if isinstance(point, dict) else point
                for row in data["rows"] for point in row.get("points", ())]
    raise ValueError("input JSON has no recognized point list")


def orbit_closure_certificate(data, *, source="", points_path=None, certificate_path=None):
    """Expand a symmetry-slice point set, explicitly without full-fibre claim."""
    start = time.monotonic()
    f = GF(data["p"], data["modulus"])
    model = Model(f, data["d"], data["tau"])
    seeds = tuple(dict.fromkeys(model.normalize_point(p) for p in extract_points(data)))
    if not seeds:
        raise ValueError("there are no seed points")
    small_model, small_seeds, embedding, descent = reduce_model_to_coordinate_subfield(model, seeds)
    ordinary_small = small_model.close_points(small_seeds)
    closed_small = small_model.close_points(ordinary_small, extended=True)
    points = tuple(tuple(tuple(embedding[a] for a in vector) for vector in point)
                   for point in closed_small)
    print(json.dumps({"stage": "seed_orbit_closure", "d": model.d, "seeds": len(seeds),
                      "ordinary_closure_points": len(ordinary_small),
                      "extended_closure_points": len(closed_small),
                      "matrix_BFS_field_q": small_model.field.q,
                      "full_fibre_complete": False,
                      "elapsed_seconds": time.monotonic() - start}), flush=True)
    small_group = small_model.clifford_group()
    if small_model is not model:
        small_group.embed_into(model, embedding)
    certificate = stabilizer_certificate(model, points, source=source)
    certificate["source_coverage"] = "Clifford closure of supplied symmetry-slice seeds only"
    certificate["full_fibre_complete"] = False
    certificate["field_descent"] = descent
    jacobians = [model.jacobian_data(point) for point in points]
    if not all(j["on_nullfiber"] for j in jacobians):
        raise ArithmeticError("a seed closure point fails the full null-fibre equations")
    frobenius = [model.frobenius_data(point) for point in points]
    output = {
        "d": model.d, "p": f.p, "q": f.q, "modulus": f.modulus,
        "tau": model.tau, "omega": model.omega, "seed": SEED,
        "python": platform.python_version(), "arithmetic": "exact finite field",
        "source": source, "source_seed_count": len(seeds),
        "coverage": "ordinary and extended Clifford closure of supplied symmetry-slice seeds only",
        "full_fibre_complete": False, "field_descent": descent,
        "ordinary_closure_points": len(ordinary_small), "extended_closure_points": len(points),
        "points": points,
        "ordinary_orbits": tuple(o["member_ids"] for o in certificate["ordinary_orbits"]),
        "extended_orbits": certificate["extended_orbits"],
        "jacobian_counts": dict(sorted(Counter(f'{j["rank_equal"]},{j["rank_null"]}'
                                                 for j in jacobians).items())),
        "absolute_coordinate_degree_counts": dict(sorted(Counter(j["absolute_coordinate_degree"]
                                                                for j in frobenius).items())),
        "tau_coefficient_degree": frobenius[0]["coefficient_degree"],
        "q0": frobenius[0]["q0"],
        "fixed_tau_Frobenius_permutation": model.frobenius_permutation(points),
        "per_point": tuple({"id": k, "point": point, "jacobian": jacobian,
                            "frobenius": frob}
                           for k, (point, jacobian, frob) in enumerate(zip(points, jacobians, frobenius))),
        "elapsed_seconds": time.monotonic() - start,
    }
    certificate["elapsed_seconds"] = output["elapsed_seconds"]
    for path, document in ((points_path, output), (certificate_path, certificate)):
        if path:
            with open(path, "w", encoding="utf-8") as handle:
                json.dump(document, handle, ensure_ascii=False, separators=(",", ":"))
                handle.write("\n")
    print(json.dumps({"stage": "seed_orbit_certificate", "d": model.d,
                      "points": len(points), "ordinary_group_order": certificate["ordinary_group_order"],
                      "ordinary_orbit_sizes": [o["ordinary_orbit_size"] for o in certificate["ordinary_orbits"]],
                      "extended_orbit_sizes": [len(o) for o in certificate["extended_orbits"]],
                      "ordinary_stabilizer_orders": [o["ordinary_stabilizer_order"] for o in certificate["ordinary_orbits"]],
                      "extended_stabilizer_orders": [o["extended_stabilizer_order"] for o in certificate["ordinary_orbits"]],
                      "jacobian_counts": output["jacobian_counts"],
                      "absolute_coordinate_degree_counts": output["absolute_coordinate_degree_counts"],
                      "full_fibre_complete": False,
                      "elapsed_seconds": output["elapsed_seconds"]}), flush=True)
    return output, certificate


def self_test():
    """Deterministic calibration, small known SICs, and requested group orders."""
    start = time.monotonic()
    rng = random.Random(SEED)
    print(json.dumps({"test": "environment", "seed": SEED, "python": sys.version,
                      "platform": platform.platform(), "arithmetic": "exact GF(p^n)",
                      "third_party_dependencies": []}), flush=True)
    f = GF(5, (2, 0, 1))
    for a in range(f.q):
        if f.encode(f.coeffs(a)) != a or f.add(a, f.neg(a)) != 0:
            raise ArithmeticError("field encoding or additive inverse failed")
        if a and f.mul(a, f.inv(a)) != 1:
            raise ArithmeticError("multiplicative inverse failed")
        for b in range(f.q):
            if f.mul(a, b) != f._raw_mul(a, b):
                raise ArithmeticError("log multiplication and polynomial multiplication disagree")
    for _ in range(300):
        a, b, c = (rng.randrange(f.q) for _ in range(3))
        if f.mul(a, f.add(b, c)) != f.add(f.mul(a, b), f.mul(a, c)):
            raise ArithmeticError("distributive law failed")
    try:
        GF(5, (1, 0, 1))
    except ValueError:
        pass
    else:
        raise ArithmeticError("reducible modulus was accepted")
    print(json.dumps({"test": "GF25", "modulus": f.modulus, "x_squared": f.mul(5, 5),
                      "all_products_checked": f.q ** 2, "distributivity_samples": 300}), flush=True)
    m2 = Model(f, 2, f.find_element_of_order(4))
    projective_line = [(1, a) for a in range(f.q)] + [(0, 1)]
    solutions = [(a, b) for a in projective_line for b in projective_line
                 if (lambda j: j["equal_overlap"] and j["t_nonzero"])(m2.jacobian_data((a, b)))]
    if len(solutions) != 8:
        raise ArithmeticError("dimension-two SIC calibration did not yield eight points")
    j2 = m2.jacobian_data(solutions[0])
    if j2["rank_equal"] != 2 or m2.orbit_partition(solutions) != (tuple(range(8)),):
        raise ArithmeticError("dimension-two calibration rank or orbit mismatch")
    g2 = m2.clifford_group()
    if g2.order != 24:
        raise ArithmeticError("dimension-two Clifford order mismatch")
    print(json.dumps({"test": "known_d2_SIC", "points": len(solutions),
                      "group_order": g2.order, "rank_equal": j2["rank_equal"],
                      "stabilizer_order": g2.stabilizer_data(solutions[0])["ordinary_stabilizer_order"]}), flush=True)
    m3 = Model(f, 3, f.find_element_of_order(3))
    hesse = ((0, 1, 4), (0, 1, 4))
    j3 = m3.jacobian_data(hesse)
    if not j3["equal_overlap"] or j3["t"] != 1 or j3["trace"] != 2:
        raise ArithmeticError("known Hesse SIC did not satisfy equal overlaps")
    if m3.clifford_group().order != 216:
        raise ArithmeticError("dimension-three Clifford order mismatch")
    print(json.dumps({"test": "known_d3_Hesse_SIC", "t": j3["t"], "trace": j3["trace"],
                      "rank_equal": j3["rank_equal"], "group_order": m3.clifford_group().order}), flush=True)
    f4 = GF(2, (1, 1, 1))
    m32 = Model(f4, 3, 2)
    j32 = m32.jacobian_data(((0, 1, 1), (0, 1, 1)))
    if not j32["on_nullfiber"] or m32.clifford_group().order != 216:
        raise ArithmeticError("odd-dimensional characteristic-two calibration failed")
    print(json.dumps({"test": "odd_dimension_char2", "d": 3, "q": 4,
                      "group_order": 216, "Hesse_on_nullfiber": True}), flush=True)
    group_tests = ((5, (2, 0, 1), 4, 5),
                   (3, irreducible_polynomial(3, 4), 5, None),
                   (7, irreducible_polynomial(7, 2), 6, None))
    directional_checks = 0
    for prime, modulus, d, tau in group_tests:
        field = GF(prime, modulus)
        tau = field.find_element_of_order(d if d % 2 else 2 * d) if tau is None else tau
        model = Model(field, d, tau)
        group = model.clifford_group()
        checks = group.verify()
        if not checks["order_matches_expected"]:
            raise ArithmeticError("computed Clifford order does not match its formula")
        swapped = model.swap_action()
        inverse_tau_model = Model(field, d, field.inv(tau))
        for g, cg in zip(model.generators(), inverse_tau_model.generators()):
            if cg.U != g.V or swapped.compose(g).compose(swapped).U != g.V:
                raise ArithmeticError("swap and tau-inversion conjugation disagree")
        for _ in range(3):
            point = tuple(tuple(rng.randrange(1, field.q) for _ in range(d)) for _ in range(2))
            directional_checks += _check_directional_jacobian(model, point, rng)
        print(json.dumps({"test": "Clifford_matrix_BFS", "d": d, "q": field.q,
                          "modulus": field.modulus, "tau": tau, "tau_order": field.order(tau),
                          "extended_order": group.extended_order, **checks}), flush=True)
    for _ in range(4):
        point = tuple(tuple(rng.randrange(1, f.q) for _ in range(4)) for _ in range(2))
        data = Model(f, 4, 5).frobenius_data(point)
        if data["coefficient_degree"] != 2 or data["q0"] != 25 or data["tau_inversion_exponents"]:
            raise ArithmeticError("GF25 cyclotomic/Frobenius distinction failed")
    print(json.dumps({"test": "derivative_and_Frobenius", "directional_rows_checked": directional_checks,
                      "GF25_tau_inversion_by_Frobenius": False}), flush=True)
    print(json.dumps({"self_test": "PASS", "elapsed_seconds": time.monotonic() - start}), flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--input", help="point-source JSON: p,modulus,d,tau plus points or per_point")
    parser.add_argument("--certificate", help="write transported stabilizer certificate JSON")
    parser.add_argument("--orbit-closure", action="store_true",
                        help="expand supplied seeds under ordinary and extended Clifford")
    parser.add_argument("--orbit-points", help="output the seed-orbit point closure JSON")
    parser.add_argument("--verify-certificate", help="independently rebuild a saved certificate")
    args = parser.parse_args(argv)
    if not (args.self_test or args.input or args.verify_certificate):
        parser.print_help()
        return 0
    if args.self_test:
        self_test()
    if args.input:
        if not args.certificate:
            parser.error("--input requires --certificate")
        start = time.monotonic()
        with open(args.input, encoding="utf-8") as handle:
            data = json.load(handle)
        if args.orbit_closure:
            if not args.orbit_points:
                parser.error("--orbit-closure requires --orbit-points")
            orbit_closure_certificate(data, source=args.input, points_path=args.orbit_points,
                                      certificate_path=args.certificate)
            return 0
        f = GF(data["p"], data["modulus"])
        tau = data.get("tau")
        if tau is None:
            tau = f.find_element_of_order(data["d"] if data["d"] % 2 else 2 * data["d"])
        model = Model(f, data["d"], tau)
        points = extract_points(data)
        certificate = stabilizer_certificate(model, points, source=args.input)
        certificate["elapsed_seconds"] = time.monotonic() - start
        with open(args.certificate, "w", encoding="utf-8") as handle:
            json.dump(certificate, handle, ensure_ascii=False, separators=(",", ":"))
            handle.write("\n")
        print(json.dumps({"certificate": args.certificate, "d": model.d,
                          "points": len(points), "ordinary_group_order": certificate["ordinary_group_order"],
                          "extended_group_order": certificate["extended_group_order"],
                          "ordinary_orbit_sizes": [o["ordinary_orbit_size"] for o in certificate["ordinary_orbits"]],
                          "ordinary_stabilizer_orders": [o["ordinary_stabilizer_order"] for o in certificate["ordinary_orbits"]],
                          "extended_stabilizer_orders": [o["extended_stabilizer_order"] for o in certificate["ordinary_orbits"]],
                          "extended_stabilizer_is_cyclic": [o["extended_stabilizer_is_cyclic"] for o in certificate["ordinary_orbits"]],
                          "fixed_actions_checked": certificate["transported_fixed_actions_checked"],
                          "elapsed_seconds": certificate["elapsed_seconds"]}), flush=True)
    if args.verify_certificate:
        start = time.monotonic()
        with open(args.verify_certificate, encoding="utf-8") as handle:
            data = json.load(handle)
        result = verify_stabilizer_certificate(data)
        print(json.dumps({"certificate": args.verify_certificate, **result,
                          "elapsed_seconds": time.monotonic() - start}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

