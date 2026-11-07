#!/usr/bin/env python3
"""Independent killer checks for the d=7, p=29 horizontal-escape claim.

Does not import the proposer's census or certificate code.
All arithmetic is exact (integers mod 29, cyclotomic integers, or Z3 reals).
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

import argparse
import gzip
import itertools
import json
import os
import time
from collections import defaultdict
from fractions import Fraction

P = 29
D = 7
T_VAR = 49
Y_VAR = 50
KNOWN_MASKS = (
    16256,
    2097024,
    266354560,
    267386752,
    268435328,
    34093399936,
)


def egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def inv(a, mod=P):
    a %= mod
    g, x, _ = egcd(a, mod)
    if g != 1:
        raise ZeroDivisionError(a)
    return x % mod


def mat_mul(A, B, mod=P):
    n = len(A)
    C = [[0] * n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k] == 0:
                continue
            aik = A[i][k]
            for j in range(n):
                C[i][j] = (C[i][j] + aik * B[k][j]) % mod
    return C


def mat_inv(A, mod=P):
    n = len(A)
    M = [A[i][:] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % mod != 0)
        M[col], M[piv] = M[piv], M[col]
        scale = inv(M[col][col], mod)
        M[col] = [(x * scale) % mod for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] % mod:
                f = M[r][col]
                M[r] = [(M[r][j] - f * M[col][j]) % mod for j in range(2 * n)]
    return [row[n:] for row in M]


def mat_vec(A, v, mod=P):
    return [sum(A[i][j] * v[j] for j in range(len(v))) % mod for i in range(len(v))]


class Cyc:
    """Element of Z[τ]/(1+τ+...+τ^6), τ^7=1, τ≠1."""

    __slots__ = ("c",)

    def __init__(self, coeffs):
        raw = [int(x) for x in coeffs]
        acc = [0] * 6
        for e, v in enumerate(raw):
            if v:
                _add_tau_pow(acc, e, v)
        self.c = tuple(acc)

    def __eq__(self, other):
        return self.c == other.c

    def __hash__(self):
        return hash(self.c)

    def __add__(self, other):
        if not isinstance(other, Cyc):
            other = Cyc([other])
        return Cyc([a + b for a, b in zip(self.c, other.c)])

    def __neg__(self):
        return Cyc([-a for a in self.c])

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Cyc):
            return Cyc([a * int(other) for a in self.c])
        raw = [0] * 12
        for i, a in enumerate(self.c):
            if a == 0:
                continue
            for j, b in enumerate(other.c):
                if b:
                    raw[i + j] += a * b
        return Cyc(raw)

    def __repr__(self):
        return f"Cyc{self.c}"

    def is_zero(self):
        return all(x == 0 for x in self.c)

    def eval_at(self, rho, mod):
        acc = 0
        pwr = 1
        for a in self.c:
            acc = (acc + a * pwr) % mod
            pwr = (pwr * rho) % mod
        return acc


def _add_tau_pow(acc, e, v):
    while e >= 6:
        base = e - 6
        for i in range(6):
            e = base + i
            v_term = -v
            if e >= 6:
                _add_tau_pow(acc, e, v_term)
            else:
                acc[e] += v_term
        return
    acc[e] += v


def tau_pow_cyc(e):
    return Cyc([1]) if e % 7 == 0 else Cyc([0] * (e % 7) + [1])


def hensel_seventh_root(rho0, digits=6):
    x = rho0 % P
    mod = P
    for _ in range(digits - 1):
        mod *= P
        fx = (pow(x, 7, mod) - 1) % mod
        fpx = (7 * pow(x, 6, mod)) % mod
        x = (x - fx * inv(fpx, mod)) % mod
    return x, mod


def valuation_p(n, mod_cap):
    if n % mod_cap == 0:
        return None  # at least the cap
    v = 0
    while n % P == 0 and n != 0:
        n //= P
        v += 1
    return v


# Polynomials: dict[tuple[tuple[int,int],...], int]  exponent key -> coeff mod P


def mon_key(factors):
    exp = defaultdict(int)
    for v in factors:
        exp[v] += 1
    if not exp:
        return ()
    return tuple(sorted(exp.items()))


def padd(a, b):
    if not b:
        return a
    if not a:
        return dict(b)
    out = dict(a)
    for k, v in b.items():
        s = (out.get(k, 0) + v) % P
        if s:
            out[k] = s
        elif k in out:
            del out[k]
    return out


def pscale(a, c):
    c %= P
    if c == 0 or not a:
        return {}
    if c == 1:
        return dict(a)
    return {k: (v * c) % P for k, v in a.items()}


def psub(a, b):
    return padd(a, pscale(b, P - 1))


def pmul(a, b):
    if not a or not b:
        return {}
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            exp = defaultdict(int)
            for v, e in ka:
                exp[v] += e
            for v, e in kb:
                exp[v] += e
            key = tuple(sorted(exp.items())) if exp else ()
            s = (out.get(key, 0) + va * vb) % P
            if s:
                out[key] = s
            elif key in out:
                del out[key]
    return out


def punit(var=None):
    if var is None:
        return {(): 1}
    return {((var, 1),): 1}


def subs_one(poly, var):
    out = {}
    for key, c in poly.items():
        exp = dict(key)
        e = exp.pop(var, 0)
        new_key = tuple(sorted(exp.items())) if exp else ()
        s = (out.get(new_key, 0) + c) % P  # var^e -> 1
        if s:
            out[new_key] = s
        elif new_key in out:
            del out[new_key]
    return out


def subs_ty_one(poly):
    return subs_one(subs_one(poly, T_VAR), Y_VAR)


def var_name_id(name):
    if name == "t":
        return T_VAR
    if name == "y":
        return Y_VAR
    if name.startswith("z") and name[1:].isdigit():
        return int(name[1:])
    raise ValueError(name)


def iter_printed_terms(text):
    """Ordered printed terms (monomial key, integer coefficient), before combining."""
    text = text.replace(" ", "").replace("\n", "")
    if text in ("", "0"):
        return []
    parts = []
    depth = 0
    sign = 1
    buf = []
    for ch in text:
        if ch == "(":
            depth += 1
            buf.append(ch)
        elif ch == ")":
            depth -= 1
            buf.append(ch)
        elif ch in "+-" and depth == 0:
            parts.append((sign, "".join(buf)))
            sign = 1 if ch == "+" else -1
            buf = []
        else:
            buf.append(ch)
    parts.append((sign, "".join(buf)))
    out = []
    for sign, body in parts:
        if body == "":
            continue
        if body.startswith("("):
            cut = body.index(")*")
            coeff = int(body[1:cut]) * sign
            rest = body[cut + 2 :]
        else:
            # bare integer coefficient: 8*t, or a pure constant 8
            i = 0
            while i < len(body) and body[i].isdigit():
                i += 1
            if i:
                coeff = int(body[:i]) * sign
                rest = body[i:]
                if rest.startswith("*"):
                    rest = rest[1:]
            else:
                coeff = sign
                rest = body
        exp = defaultdict(int)
        if rest not in ("", "1"):
            for fac in rest.split("*"):
                if fac in ("", "1"):
                    continue
                if fac.isdigit():
                    coeff *= int(fac)
                    continue
                if "^" in fac:
                    base, e = fac.split("^")
                    exp[var_name_id(base)] += int(e)
                else:
                    exp[var_name_id(fac)] += 1
        key = tuple(sorted(exp.items())) if exp else ()
        out.append((key, coeff))
    return out


def parse_poly(text):
    acc = {}
    for key, coeff in iter_printed_terms(text):
        s = (acc.get(key, 0) + coeff) % P
        if s:
            acc[key] = s
        elif key in acc:
            del acc[key]
    return acc


def poly_eq(a, b):
    return a == b


def mon_labels(key):
    labs = []
    for v, e in key:
        if v >= T_VAR:
            return None
        labs.extend([v] * e)
    return tuple(labs)


def mon_degree(key):
    return sum(e for _, e in key)


def term_weight(key, weights, wt, wy):
    total = 0
    for v, e in key:
        if v <= 48:
            total += e * weights[v]
        elif v == T_VAR:
            total += e * wt
        else:
            total += e * wy
    return total


def initial_form(poly, weights, mu):
    if not poly:
        return {}, None
    best = None
    grouped = []
    for key, c in poly.items():
        tw = term_weight(key, weights, mu, -mu)
        grouped.append((tw, key, c))
        if best is None or tw < best:
            best = tw
    out = {}
    for tw, key, c in grouped:
        if tw == best:
            out[key] = c
    return out, best


def homogenize_chart(poly, z_first, target_deg=2):
    out = {}
    for key, c in poly.items():
        deg = mon_degree(key)
        exp = dict(key)
        need = target_deg - deg
        if need < 0:
            return None
        if need:
            exp[z_first] = exp.get(z_first, 0) + need
        new_key = tuple(sorted(exp.items())) if exp else ()
        out[new_key] = c
    return out


def opp_label(q):
    r, k = divmod(q, D)
    return ((-r) % D) * D + ((-k) % D)


def mask_of(labels):
    m = 0
    for q in labels:
        m |= 1 << q
    return m


def iter_mask(mask):
    for q in range(49):
        if mask >> q & 1:
            yield q


def describe_mask(mask):
    rows = {}
    for q in iter_mask(mask):
        r, k = divmod(q, D)
        rows.setdefault(r, []).append(k)
    return {r: sorted(ks) for r, ks in sorted(rows.items())}


class Weyl:
    def __init__(self, tau):
        self.tau = tau % P
        self.omega = pow(self.tau, 2, P)
        self.D = []
        for r in range(D):
            for k in range(D):
                M = [[0] * D for _ in range(D)]
                for j in range(D):
                    M[(j + r) % D][j] = pow(self.tau, (r * k + 2 * k * j) % D, P)
                self.D.append(M)
        self._lin = []
        for i in range(D):
            row = []
            for j in range(D):
                r = (i - j) % D
                form = {}
                for k in range(D):
                    q = r * D + k
                    form[q] = self.D[q][i][j]
                row.append(form)
            self._lin.append(row)

    def z_coeffs(self, a, b):
        """Weyl coefficients c with Σ c_q D_q = 7 ab^T."""
        z = [0] * 49
        tau = self.tau
        for r in range(D):
            for k in range(D):
                s = 0
                phase_base = (-k * r) % D
                for j in range(D):
                    aj = a[(j + r) % D]
                    bj = b[j]
                    if aj == 0 or bj == 0:
                        continue
                    s = (s + aj * bj * pow(tau, (phase_base - 2 * k * j) % D, P)) % P
                z[r * D + k] = s
        return z

    def direct_Z(self, a, b, r, k):
        acc = 0
        for j in range(D):
            coeff = pow(self.tau, (r * k + 2 * k * j) % D, P)
            acc = (acc + b[(j + r) % D] * coeff * a[j]) % P
        return acc

    def matrix_from_z(self, z):
        M = [[0] * D for _ in range(D)]
        for q, c in enumerate(z):
            if c == 0:
                continue
            Dq = self.D[q]
            for i in range(D):
                for j in range(D):
                    if Dq[i][j]:
                        M[i][j] = (M[i][j] + c * Dq[i][j]) % P
        return M

    def abT(self, a, b):
        return [[(a[i] * b[j]) % P for j in range(D)] for i in range(D)]

    def minors(self):
        polys = []
        for i1, i2 in itertools.combinations(range(D), 2):
            for j1, j2 in itertools.combinations(range(D), 2):
                polys.append(self._minor_poly(i1, i2, j1, j2))
        return polys

    def _det_of_forms(self, f11, f22, f12, f21):
        # f11*f22 - f12*f21, linear forms as dict label->coeff in F_p
        acc = {}

        def add_prod(f, g, sign):
            for q, cq in f.items():
                if cq == 0:
                    continue
                for r, cr in g.items():
                    if cr == 0:
                        continue
                    key = mon_key([q, r])
                    s = (acc.get(key, 0) + sign * cq * cr) % P
                    if s:
                        acc[key] = s
                    elif key in acc:
                        del acc[key]

        add_prod(f11, f22, 1)
        add_prod(f12, f21, P - 1)
        return acc

    def _minor_poly(self, i1, i2, j1, j2):
        return self._det_of_forms(
            self._lin[i1][j1],
            self._lin[i2][j2],
            self._lin[i1][j2],
            self._lin[i2][j1],
        )

    def square_polys(self):
        """Coefficients of (Σ z_q D_q)^2 - 7 z_0 (Σ z_q D_q), one poly per output label."""
        chi = [[0] * 49 for _ in range(49)]
        target = [[0] * 49 for _ in range(49)]
        for p in range(49):
            for q in range(49):
                prod = mat_mul(self.D[p], self.D[q])
                lab, phase = identify_weyl(prod, self.D)
                if lab is None:
                    raise RuntimeError(f"D_{p} D_{q} not Weyl")
                target[p][q] = lab
                chi[p][q] = phase
        polys = []
        for s in range(49):
            acc = {}
            for p in range(49):
                for q in range(49):
                    if target[p][q] != s:
                        continue
                    key = mon_key([p, q])
                    scoeff = (acc.get(key, 0) + chi[p][q]) % P
                    if scoeff:
                        acc[key] = scoeff
                    elif key in acc:
                        del acc[key]
            # subtract 7 z_0 z_s
            key = mon_key([0, s])
            scoeff = (acc.get(key, 0) - (7 % P)) % P
            if scoeff:
                acc[key] = scoeff
            elif key in acc:
                del acc[key]
            polys.append(acc)
        return polys

    def minors_cyc(self):
        """Same minors with cyclotomic integer coefficients. Entry phase τ^{rk+2kj}."""
        tau = tau_pow_cyc(1)
        lins = []
        for i in range(D):
            row = []
            for j in range(D):
                r = (i - j) % D
                form = {}
                for k in range(D):
                    q = r * D + k
                    form[q] = tau_pow_cyc((r * k + 2 * k * j) % D)
                row.append(form)
            lins.append(row)
        polys = []
        zero = Cyc([])
        for i1, i2 in itertools.combinations(range(D), 2):
            for j1, j2 in itertools.combinations(range(D), 2):
                acc = {}

                def add_prod(f, g, sign):
                    for q, cq in f.items():
                        for r, cr in g.items():
                            key = mon_key([q, r])
                            term = (cq * cr) if sign == 1 else -(cq * cr)
                            acc[key] = term if key not in acc else acc[key] + term

                add_prod(lins[i1][j1], lins[i2][j2], 1)
                add_prod(lins[i1][j2], lins[i2][j1], -1)
                acc = {k: v for k, v in acc.items() if not v.is_zero()}
                polys.append(acc)
        return polys


def identify_weyl(M, Ds):
    for q, Dq in enumerate(Ds):
        ratio = None
        ok = True
        for i in range(D):
            for j in range(D):
                if Dq[i][j] == 0:
                    if M[i][j] % P != 0:
                        ok = False
                        break
                else:
                    if M[i][j] % P == 0:
                        ok = False
                        break
                    rr = (M[i][j] * inv(Dq[i][j])) % P
                    if ratio is None:
                        ratio = rr
                    elif ratio != rr:
                        ok = False
                        break
            if not ok:
                break
        if ok and ratio is not None:
            return q, ratio
    return None, None


def C_rs(a, b, r, s):
    tot = 0
    for i in range(D):
        tot = (
            tot
            + a[i]
            * b[(i + r) % D]
            * b[(i + s) % D]
            * a[(i + r + s) % D]
        ) % P
    return tot


def all_C_zero(a, b):
    for r in range(D):
        for s in range(D):
            if C_rs(a, b, r, s) != 0:
                return False
    return True


def support_of_z(z):
    return [q for q, c in enumerate(z) if c]


def projections_of(poly):
    buckets = defaultdict(dict)
    for key, c in poly.items():
        labs = mon_labels(key)
        if labs is None:
            continue
        total = 0
        for q in labs:
            total = (total + q_add(total and 0 or 0, q)) if False else None
        acc_r, acc_k = 0, 0
        for q in labs:
            r, k = divmod(q, D)
            acc_r = (acc_r + r) % D
            acc_k = (acc_k + k) % D
        mom = acc_r * D + acc_k
        buckets[mom][key] = c
    return list(buckets.values())


def q_add(a, b):
    return (a + b) % D


def pattern_of(poly, kill_z0=True):
    mons = []
    for key, c in poly.items():
        if c % P == 0:
            continue
        labs = mon_labels(key)
        if labs is None:
            continue
        if kill_z0 and 0 in labs:
            continue
        if any(v >= T_VAR for v, _ in key):
            continue
        mons.append(tuple(sorted(labs)))
    if not mons:
        return None
    return tuple(sorted(set(mons)))


def forbid_clause_data(pattern):
    return pattern


def build_base_patterns(weyl: Weyl):
    pats = set()
    n_src = 0
    for poly in weyl.minors():
        n_src += 1
        for proj in projections_of(poly):
            pat = pattern_of(proj)
            if pat:
                pats.add(pat)
    squares = weyl.square_polys()
    for poly in squares:
        n_src += 1
        for proj in projections_of(poly):
            pat = pattern_of(proj)
            if pat:
                pats.add(pat)
    return pats, n_src, squares


def perm_pattern(pat, perm):
    mons = []
    for mon in pat:
        mons.append(tuple(sorted(perm[q] for q in mon)))
    return tuple(sorted(set(mons)))


def close_patterns(pats, perms):
    closed = set(pats)
    for perm in perms:
        for pat in pats:
            closed.add(perm_pattern(pat, perm))
    return closed


def conj_perm(U, weyl: Weyl):
    Uinv = mat_inv(U)
    perm = [None] * 49
    for q in range(49):
        M = mat_mul(mat_mul(U, weyl.D[q]), Uinv)
        lab, _phase = identify_weyl(M, weyl.D)
        if lab is None:
            return None
        perm[q] = lab
    if len(set(perm)) != 49:
        return None
    return tuple(perm)


def generate_group(weyl: Weyl):
    tau = weyl.tau
    omega = weyl.omega
    gens = []
    # clock shift X
    X = [[0] * D for _ in range(D)]
    for j in range(D):
        X[(j + 1) % D][j] = 1
    gens.append(X)
    # quadratic shears
    for c in range(1, D):
        Q = [[0] * D for _ in range(D)]
        for j in range(D):
            Q[j][j] = pow(tau, (c * j * j) % D, P)
        gens.append(Q)
    # Fourier without the global scalar
    F = [[pow(omega, (i * j) % D, P) for j in range(D)] for i in range(D)]
    gens.append(F)
    Fm = [[pow(omega, (-i * j) % D, P) for j in range(D)] for i in range(D)]
    gens.append(Fm)
    # parity j -> -j
    Par = [[0] * D for _ in range(D)]
    for j in range(D):
        Par[(-j) % D][j] = 1
    gens.append(Par)

    perms = []
    failed = 0
    for U in gens:
        try:
            _ = mat_inv(U)
        except ZeroDivisionError:
            failed += 1
            continue
        perm = conj_perm(U, weyl)
        if perm is None:
            failed += 1
        else:
            perms.append(perm)
    # BFS closure
    idp = tuple(range(49))
    group = {idp: idp}
    queue = [idp]
    gen_perms = perms
    cap = 4000
    while queue and len(group) < cap:
        cur = queue.pop()
        for g in gen_perms:
            nxt = tuple(g[cur[i]] for i in range(49))
            if nxt not in group:
                group[nxt] = nxt
                queue.append(nxt)
                if len(group) >= cap:
                    break
            nxt2 = tuple(cur[g[i]] for i in range(49))
            if nxt2 not in group and len(group) < cap:
                group[nxt2] = nxt2
                queue.append(nxt2)
    return list(group.keys()), failed, len(gen_perms)


def apply_perm_mask(mask, perm):
    out = 0
    for q in iter_mask(mask):
        out |= 1 << perm[q]
    return out


def orbit_masks(mask, perms):
    seen = set()
    for perm in perms:
        seen.add(apply_perm_mask(mask, perm))
    return seen


def passes_patterns(mask, patterns):
    selected = [(mask >> q & 1) == 1 for q in range(49)]
    if selected[0]:
        return False
    for q in range(49):
        if selected[q] and selected[opp_label(q)] and q != opp_label(q):
            return False
    for pat in patterns:
        active = 0
        for mon in pat:
            if all(selected[q] for q in mon):
                active += 1
                if active > 1:
                    break
        if active == 1:
            return False
    return True


def sl2_left_perms():
    """Label permutation (r,k) |-> F (r,k)^T for F in SL2, as a cross-check."""
    perms = []
    for a, b, c, d in itertools.product(range(D), repeat=4):
        if (a * d - b * c) % D != 1:
            continue
        perm = [0] * 49
        for r in range(D):
            for k in range(D):
                nr = (a * r + b * k) % D
                nk = (c * r + d * k) % D
                perm[r * D + k] = nr * D + nk
        perms.append(tuple(perm))
    return perms


def full_row_witness(U, weyl: Weyl):
    """A={0}, B=-U, a=e_0, b=1 on B. U subset of F_7^*, U intersect -U empty."""
    B = [(-r) % D for r in U]
    if 0 in B or any(((-b) % D) in B for b in B):
        return None
    a = [0] * D
    b = [0] * D
    a[0] = 1
    for j in B:
        b[j] = 1
    if not all_C_zero(a, b):
        return None
    z = weyl.z_coeffs(a, b)
    return a, b, z


def explicit_hole_candidates(weyl: Weyl):
    found = {}
    omega = weyl.omega
    trials = []
    base_a = [1, 1, 0, 0, 0, 0, 0]
    b = [0] * D
    b[5] = 1
    b[6] = (-pow(omega, 6, P)) % P
    trials.append((base_a[:], b[:]))
    # small search |A|,|B| >= 2, free vars <= 3, 0 in A
    subsets = []
    for n in range(D + 1):
        subsets.extend(itertools.combinations(range(D), n))
    A_list = [A for A in subsets if A and 0 in A and 2 <= len(A) <= 4]
    B_list = [B for B in subsets if B and 2 <= len(B) <= 4]
    for A in A_list:
        for B in B_list:
            free_a = list(A[1:])  # A[0] is 0, fixed to 1
            free_b = list(B[1:])
            if len(free_a) + len(free_b) > 2:
                continue
            ranges = [range(1, P) for _ in free_a + free_b]
            for vals in itertools.product(*ranges):
                a = [0] * D
                b = [0] * D
                a[A[0]] = 1
                for i, v in enumerate(free_a):
                    a[v] = vals[i]
                b[B[0]] = 1
                for i, v in enumerate(free_b):
                    b[v] = vals[len(free_a) + i]
                if not all_C_zero(a, b):
                    continue
                z = weyl.z_coeffs(a, b)
                m = mask_of(support_of_z(z))
                if m not in found:
                    found[m] = (a[:], b[:], z)
    for a, b in trials:
        if all_C_zero(a, b):
            z = weyl.z_coeffs(a, b)
            m = mask_of(support_of_z(z))
            found.setdefault(m, (a[:], b[:], z))
    return found


def z3_exclude(patterns, masks, threads=8, min_size=7):
    from z3 import And, AtLeast, Bool, Not, Or, PbEq, Solver, sat, unsat

    s = Solver()
    s.set("threads", threads)
    s.set("max_memory", 40000)
    sel = [Bool(f"s{q}") for q in range(49)]
    s.add(Not(sel[0]))
    # |S|>=d is forced by the left-ideal argument; the empty set is not a point of P x P.
    if min_size:
        s.add(AtLeast(*sel, min_size))
    seen_pairs = set()
    for q in range(1, 49):
        o = opp_label(q)
        pair = (q, o) if q < o else (o, q)
        if q == o or pair in seen_pairs:
            continue
        seen_pairs.add(pair)
        s.add(Not(And(sel[q], sel[o])))
    aux_n = 0
    for pat in patterns:
        acts = []
        for mon in pat:
            if len(mon) == 1:
                acts.append(sel[mon[0]])
            elif len(mon) == 2:
                b = Bool(f"m{aux_n}")
                aux_n += 1
                s.add(b == And(sel[mon[0]], sel[mon[1]]))
                acts.append(b)
            else:
                b = Bool(f"m{aux_n}")
                aux_n += 1
                s.add(b == And([sel[q] for q in mon]))
                acts.append(b)
        if len(acts) == 1:
            s.add(Not(acts[0]))
        elif len(acts) >= 2:
            s.add(Not(PbEq([(a, 1) for a in acts], 1)))
    for mask in masks:
        lits = []
        for q in range(49):
            bit = (mask >> q & 1) == 1
            lits.append(sel[q] if bit else Not(sel[q]))
        s.add(Not(And(lits)))
    t0 = time.time()
    result = s.check()
    dt = time.time() - t0
    extra = None
    if result == sat:
        model = s.model()
        extra_mask = 0
        for q in range(49):
            if model.eval(sel[q], model_completion=True) == True or str(
                model.eval(sel[q], model_completion=True)
            ) == "True":
                # z3.BoolRef truth
                val = model.evaluate(sel[q], model_completion=True)
                if val == True or (hasattr(val, "sexpr") and val.sexpr() == "true"):
                    extra_mask |= 1 << q
        # robust eval
        extra_mask = 0
        for q in range(49):
            val = model.evaluate(sel[q], model_completion=True)
            if is_true_z3(val):
                extra_mask |= 1 << q
        extra = extra_mask
    return str(result), dt, extra, aux_n


def is_true_z3(val):
    return str(val) == "True"


def self_test(weyl: Weyl):
    report = {}
    # cyclotomic τ^7 = 1
    one = tau_pow_cyc(0)
    tau7 = tau_pow_cyc(7)
    report["tau7_is_1"] = tau7 == one
    # reconstruction Σ c D = 7 ab^T
    a = [1, 2, 0, 3, 0, 0, 4]
    b = [0, 5, 1, 0, 0, 2, 0]
    z = weyl.z_coeffs(a, b)
    M = weyl.matrix_from_z(z)
    AB = weyl.abT(a, b)
    seven = [[(7 * AB[i][j]) % P for j in range(D)] for i in range(D)]
    report["reconstruction_7abT"] = M == seven
    # c_q vs Z_{-q}
    match_Z = True
    for r in range(D):
        for k in range(D):
            Z = weyl.direct_Z(a, b, r, k)
            c = z[((-r) % D) * D + ((-k) % D)]
            if Z != c:
                match_Z = False
    report["c_q_equals_Z_minus_q"] = match_Z
    # minors vanish on this rank-1 point
    def eval_quad(poly, z):
        acc = 0
        for key, c in poly.items():
            term = c
            for v, e in key:
                term = term * pow(z[v], e, P) % P
            acc = (acc + term) % P
        return acc

    minors = weyl.minors()
    report["n_minors"] = len(minors)
    report["minors_vanish_on_rank1"] = all(eval_quad(f, z) == 0 for f in minors)
    squares = weyl.square_polys()
    report["n_squares"] = len(squares)
    report["squares_vanish_on_rank1"] = all(eval_quad(f, z) == 0 for f in squares)
    # full row witness
    a1, b1, z1 = full_row_witness([1], weyl)
    report["row_witness_C"] = all_C_zero(a1, b1)
    report["row_witness_mask"] = mask_of(support_of_z(z1))
    report["row_witness_desc"] = describe_mask(report["row_witness_mask"])
    report["products_zero_on_row"] = all(
        z1[q] == 0 or z1[opp_label(q)] == 0 for q in range(49)
    )
    report["z0_zero_on_row"] = z1[0] == 0
    # parser
    samples = {
        "ty": parse_poly("t*y-1"),
        "prod": parse_poly("(28)*t+(1)*z1*z6"),
        "lin": parse_poly("(1)*1+(13)*z13"),
        "z0": parse_poly("(28)*z0*1"),
        "trace": parse_poly("(21)*t+(1)*z0*z0"),
        "bare": parse_poly("(1)*z1*z6-8*t"),
        "pow": parse_poly("(1)*z0^2-8*t"),
    }
    report["parse_ty"] = samples["ty"] == {((T_VAR, 1), (Y_VAR, 1)): 1, (): P - 1}
    report["parse_prod"] = samples["prod"] == {
        ((T_VAR, 1),): P - 1,
        ((1, 1), (6, 1)): 1,
    }
    report["parse_trace_is_z0sq_minus_8t"] = samples["trace"] == {
        ((T_VAR, 1),): (-8) % P,
        ((0, 2),): 1,
    }
    report["parse_bare_coeff"] = samples["bare"] == {
        ((1, 1), (6, 1)): 1,
        ((T_VAR, 1),): (-8) % P,
    }
    report["parse_pow"] = samples["pow"] == samples["trace"]
    return report


def support_census(weyl: Weyl, threads):
    t0 = time.time()
    perms, failed_gens, n_ok_gens = generate_group(weyl)
    # compare with abstract SL2
    abstract = sl2_left_perms()
    abstract_set = set(abstract)
    conj_set = set(perms)
    # try inverse convention: perm_inv
    inv_perms = []
    for perm in perms:
        inv = [0] * 49
        for i, j in enumerate(perm):
            inv[j] = i
        inv_perms.append(tuple(inv))
    print("group", len(perms), "failed_gens", failed_gens, flush=True)
    patterns, n_src, _squares = build_base_patterns(weyl)
    print("base patterns", len(patterns), flush=True)
    closed = close_patterns(patterns, perms)
    print("closed patterns", len(closed), flush=True)
    # witnesses
    witnesses = {}
    for mask_bits in range(1, 8):
        U = [i for i in range(1, 7) if mask_bits >> (i - 1) & 1]
        # U as subset of {1,2,3,4,5,6} without opposite pairs — enumerate properly below
    seeds = []
    for r in range(1, 7):
        for s in range(r + 1, 7):
            pass
    nonempty_U = []
    for n in (1, 2, 3):
        for U in itertools.combinations([1, 2, 3, 4, 5, 6], n):
            if any(((-u) % D) in U for u in U):
                continue
            wit = full_row_witness(list(U), weyl)
            if wit is None:
                continue
            a, b, z = wit
            m = mask_of(support_of_z(z))
            seeds.append({"kind": "full-rows", "U": list(U), "mask": m, "a": a, "b": b})
    holes = explicit_hole_candidates(weyl)
    for m, (a, b, z) in holes.items():
        seeds.append(
            {
                "kind": "search",
                "mask": m,
                "a": a,
                "b": b,
                "size": bin(m).count("1"),
                "desc": describe_mask(m),
            }
        )
    # orbits of seeds under conjugation group
    seed_orbits = []
    covered = set()
    for sd in seeds:
        orb = orbit_masks(sd["mask"], perms)
        if sd["mask"] in covered:
            continue
        covered |= orb
        seed_orbits.append(
            {
                "seed_mask": sd["mask"],
                "kind": sd["kind"],
                "size": bin(sd["mask"]).count("1"),
                "orbit": len(orb),
                "desc": describe_mask(sd["mask"]),
            }
        )
    # orbits of the six published masks
    published = []
    pub_union = set()
    for m in KNOWN_MASKS:
        orb = orbit_masks(m, perms)
        pub_union |= orb
        published.append(
            {
                "mask": m,
                "orbit": len(orb),
                "size": bin(m).count("1"),
                "desc": describe_mask(m),
                "in_seed_covered": m in covered,
            }
        )
    # which published orbit sizes arise from abstract SL2 as well
    published_abstract = []
    for m in KNOWN_MASKS:
        orb = orbit_masks(m, abstract)
        published_abstract.append({"mask": m, "orbit": len(orb), "size": bin(m).count("1")})

    seed_union = covered
    # Z3: anything outside the published orbits under THIS conjugation group,
    # and also outside the abstract SL2 orbits of the six masks.
    abs_union = set()
    for m in KNOWN_MASKS:
        abs_union |= orbit_masks(m, abstract)
    # Use the larger of the two group closures as the "claimed 544" only after size check.
    claimed = abs_union if len(abs_union) >= len(pub_union) else pub_union
    # Verify every claimed mask passes closed patterns. A failure means either the
    # pattern set is too strong (bug) or the mask is not a real support.
    bad_claimed = []
    for m in list(claimed)[:]:
        if not passes_patterns(m, closed):
            bad_claimed.append(m)
    if len(closed) > 20000:
        z3_status, z3_dt, extra, aux_n = "skipped-too-many-patterns", 0, None, 0
    else:
        print("z3 closed", len(closed), "blocking", len(claimed), flush=True)
        z3_status, z3_dt, extra, aux_n = z3_exclude(closed, claimed, threads=threads)
        print("z3 closed result", z3_status, z3_dt, flush=True)
    extras = []
    if extra is not None:
        # pull a few extras by repeating is unnecessary; record this one and whether
        # it passes only the unclosed patterns
        extras.append(
            {
                "mask": extra,
                "size": bin(extra).count("1"),
                "desc": describe_mask(extra),
                "passes_closed": passes_patterns(extra, closed),
                "passes_base": passes_patterns(extra, patterns),
            }
        )
    # unclosed extras: Z3 on base patterns only, blocked by claimed, but that can be SAT
    # with ghosts. Record one ghost if present, without treating it as a support.
    print("z3 base", len(patterns), flush=True)
    z3_base_status, z3_base_dt, base_extra, _ = z3_exclude(patterns, claimed, threads=threads)
    print("z3 base result", z3_base_status, z3_base_dt, flush=True)
    ghost = None
    if base_extra is not None:
        ghost = {
            "mask": base_extra,
            "size": bin(base_extra).count("1"),
            "desc": describe_mask(base_extra),
            "passes_base": True,
            "passes_closed": passes_patterns(base_extra, closed),
        }
    return {
        "seconds": time.time() - t0,
        "tau": weyl.tau,
        "group_conjugation_order": len(perms),
        "group_generators_ok": n_ok_gens,
        "group_generators_failed": failed_gens,
        "abstract_SL2_order": len(abstract),
        "conjugation_equals_some_SL2_action": conj_set == abstract_set
        or set(inv_perms) == abstract_set,
        "base_patterns": len(patterns),
        "closed_patterns": len(closed),
        "source_polys": n_src,
        "z3_aux_bools": aux_n,
        "seed_orbit_summary": seed_orbits,
        "seed_union": len(seed_union),
        "published_under_conjugation": published,
        "published_under_abstract_SL2": published_abstract,
        "published_union_conjugation": len(pub_union),
        "published_union_abstract": len(abs_union),
        "claimed_blocked": len(claimed),
        "claimed_fail_closed_patterns": [describe_mask(m) for m in bad_claimed[:8]],
        "n_claimed_fail": len(bad_claimed),
        "z3_closed_outside_claimed": z3_status,
        "z3_closed_seconds": z3_dt,
        "z3_extra": extras,
        "z3_base_outside_claimed": z3_base_status,
        "z3_base_seconds": z3_base_dt,
        "base_ghost_example": ghost,
        "n_explicit_rank1_masks": len({s["mask"] for s in seeds}),
        "explicit_masks_outside_claimed": [
            {"mask": m, "size": bin(m).count("1"), "desc": describe_mask(m)}
            for m in holes
            if m not in claimed
        ],
        "hole_masks_found": [
            {"mask": m, "size": bin(m).count("1"), "desc": describe_mask(m)}
            for m, _ in holes.items()
        ],
    }


def coefficient_valuations(tau_for_model):
    """Valuations of minor coefficients at all six primes above 29."""
    weyl_c = Weyl(tau_for_model)
    polys = weyl_c.minors_cyc()
    roots = [x for x in range(1, P) if pow(x, D, P) == 1 and x != 1]
    lifts = {rho: hensel_seventh_root(rho, 4) for rho in roots}
    hist = {rho: defaultdict(int) for rho in roots}
    examples = []
    n_coeff = 0
    n_unit_all = 0
    n_some_positive = 0
    for poly in polys:
        for key, cyc in poly.items():
            if cyc.is_zero():
                continue
            n_coeff += 1
            vals = {}
            any_pos = False
            for rho in roots:
                lift, mod = lifts[rho]
                # evaluate Σ a_i lift^i in Z/mod, then valuation
                acc = 0
                pwr = 1
                for a in cyc.c:
                    acc += a * pwr
                    pwr *= lift
                acc %= mod
                if acc == 0:
                    v = 4  # at least
                else:
                    v = 0
                    while acc % P == 0:
                        acc //= P
                        v += 1
                vals[rho] = v
                hist[rho][v] += 1
                if v > 0:
                    any_pos = True
            if any_pos:
                n_some_positive += 1
                if len(examples) < 12:
                    examples.append({"monomial": key, "valuations": vals, "cyc": cyc.c})
            else:
                n_unit_all += 1
    return {
        "n_minor_coefficients": n_coeff,
        "n_unit_at_all_six_primes": n_unit_all,
        "n_positive_at_some_prime": n_some_positive,
        "roots": roots,
        "histogram": {str(rho): dict(hist[rho]) for rho in roots},
        "examples": examples,
        "working_tau": tau_for_model,
    }


def load_json_gz(data_dir, files):
    blob = b"".join(open(os.path.join(data_dir, fn), "rb").read() for fn in files)
    return json.loads(gzip.decompress(blob))


def load_merge_certificates(data_dir):
    merge = json.load(open(os.path.join(data_dir, "e33_merge_p29.json")))
    certs = []
    for block in merge["results"]:
        for ident in block["authenticated_identities"]:
            certs.append(
                {
                    "mask": block["mask"],
                    "orbit_index": block["orbit_index"],
                    "kind": ident["certificate_kind"],
                    "files": ident["manifest"]["files"],
                    "sha256": ident["manifest"]["uncompressed_sha256"],
                    "claimed_multipliers": ident.get("nonzero_multipliers")
                    or ident.get("reduced_nonzero_multipliers"),
                }
            )
    return merge["status"], certs


def grades_of(cert):
    g = cert["grading"]["integer_grading"]
    grade = {}
    for name, val in g.items():
        grade[var_name_id(name)] = int(val)
    return grade, int(cert["grading"]["t_grade"])


def is_homogeneous(poly, grade):
    degs = set()
    for key, _c in poly.items():
        deg = 0
        for v, e in key:
            if v not in grade:
                return False, None
            deg += e * grade[v]
        degs.add(deg)
    if not degs:
        return True, None
    if len(degs) != 1:
        return False, degs
    return True, next(iter(degs))


def chart_polys(weyl: Weyl, z_first):
    """Full model polynomials in the z_first=1 chart, tagged."""
    tagged = []
    for i, poly in enumerate(weyl.minors()):
        tagged.append(("minor", i, subs_one(poly, z_first)))
    squares = weyl.square_polys()
    # drop the output-label 0 square; the trace relation is stored separately
    for i, poly in enumerate(squares):
        if i == 0:
            continue
        tagged.append(("square", i, subs_one(poly, z_first)))
    return tagged


def product_polys(z_first):
    polys = []
    seen = set()
    for q in range(1, 49):
        o = opp_label(q)
        pair = tuple(sorted((q, o)))
        if pair in seen or q == o:
            continue
        seen.add(pair)
        # z_q z_{-q} - t, with z_first substituted by 1
        key = mon_key([q, o])
        poly = {key: 1, ((T_VAR, 1),): P - 1}
        poly = subs_one(poly, z_first)
        polys.append((pair, poly))
    trace = {((0, 2),): 1, ((T_VAR, 1),): (-8) % P}
    trace = subs_one(trace, z_first)
    ty = {((T_VAR, 1), (Y_VAR, 1)): 1, (): P - 1}
    return polys, trace, ty


def block_relation_polys(weyl: Weyl, A, B, z_first):
    """Linear forms of residual matrix entries outside A×B, then z_first=1."""
    rels = []
    Aset, Bset = set(A), set(B)
    for i in range(D):
        for j in range(D):
            if i in Aset and j in Bset:
                continue
            form = dict(weyl._lin[i][j])
            # keep only labels; this linear form equals the matrix entry of Σ z D
            poly = {}
            for q, c in form.items():
                if c % P == 0:
                    continue
                poly[mon_key([q])] = c % P
            poly = subs_one(poly, z_first)
            if poly:
                rels.append(poly)
    # row-reduce and drop zero rows, return a basis
    basis = rref_polys(rels)
    return basis


def rref_polys(rels):
    # linear polynomials only: constant + sum c_q z_q
    rows = []
    for poly in rels:
        const = poly.get((), 0) % P
        coeffs = {}
        ok = True
        for key, c in poly.items():
            if key == ():
                continue
            if mon_degree(key) != 1:
                ok = False
                break
            (v, e), = key
            coeffs[v] = c % P
        if ok:
            rows.append((const, coeffs))
    if not rows:
        return []
    # variables
    vars_ = sorted({v for _, coeffs in rows for v in coeffs})
    # gaussian elimination
    col_of = {v: i for i, v in enumerate(vars_)}
    n = len(vars_)
    M = []
    for const, coeffs in rows:
        row = [0] * (n + 1)
        for v, c in coeffs.items():
            row[col_of[v]] = c % P
        row[n] = const % P
        M.append(row)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % P != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        scale = inv(M[r][c])
        M[r] = [(x * scale) % P for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % P:
                f = M[i][c]
                M[i] = [(M[i][j] - f * M[r][j]) % P for j in range(n + 1)]
        r += 1
        if r == len(M):
            break
    out = []
    for row in M:
        if all(x % P == 0 for x in row):
            continue
        poly = {}
        for i, v in enumerate(vars_):
            if row[i] % P:
                poly[mon_key([v])] = row[i] % P
        if row[n] % P:
            poly[()] = row[n] % P
        out.append(poly)
    return out


def linear_span_basis(polys):
    """An echelon basis over F_29, including the chart's constant column."""
    basis = {}
    for poly in polys:
        if any(key and (len(key) != 1 or key[0][1] != 1) for key in poly):
            raise ValueError("nonlinear polynomial in the block relation space")
        row = dict(poly)
        for pivot, reducer in sorted(basis.items()):
            if row.get(pivot, 0):
                row = psub(row, pscale(reducer, row[pivot]))
        if row:
            pivot = min(row)
            basis[pivot] = pscale(row, inv(row[pivot]))
    return sorted(basis.items())


def linear_in_span(poly, basis):
    """Reject nonlinear forms, then reduce every coefficient exactly mod 29."""
    if any(key and (len(key) != 1 or key[0][1] != 1) for key in poly):
        return False
    row = dict(poly)
    for pivot, reducer in basis:
        if row.get(pivot, 0):
            row = psub(row, pscale(reducer, row[pivot]))
    return not row


def check_unmatched_block_span(indexed_polys, block_basis):
    unexplained = [i for i, poly in indexed_polys if not linear_in_span(poly, block_basis)]
    return {
        "unmatched_linear_in_block_span": len(indexed_polys) - len(unexplained),
        "unmatched_not_explained": unexplained,
    }


def index_model(weyl, z_first, A, B, weights, mu):
    """Map each chart-initial-form and each auxiliary polynomial to a hash."""
    table = {}
    parents = {}
    for kind, idx, poly in chart_polys(weyl, z_first):
        init, _ = initial_form(poly, weights, mu)
        h = poly_hash(init)
        table.setdefault(h, []).append((kind, idx, "initial"))
        parents[(kind, idx)] = poly
    prods, trace, ty = product_polys(z_first)
    for pair, poly in prods:
        table.setdefault(poly_hash(poly), []).append(("product", pair, "full"))
    table.setdefault(poly_hash(trace), []).append(("trace", None, "full"))
    table.setdefault(poly_hash(ty), []).append(("ty", None, "full"))
    for poly in block_relation_polys(weyl, A, B, z_first):
        table.setdefault(poly_hash(poly), []).append(("block", None, "full"))
    # also index full chart polys (not just initial forms): a stored generator
    # might be the whole chart polynomial
    for kind, idx, poly in chart_polys(weyl, z_first):
        table.setdefault(poly_hash(poly), []).append((kind, idx, "full-chart"))
    return table, parents, prods, trace, ty


def poly_hash(poly):
    return tuple(sorted((k, c % P) for k, c in poly.items()))


def parse_weights(cert):
    w = [Fraction(x) for x in cert["weights"]]
    mu = Fraction(cert["mu"])
    return w, mu


def replay_flat(cert, table, block_basis):
    acc = {}
    unmatched = []
    unmatched_polys = []
    matched = []
    for mem in cert["members"]:
        gen = parse_poly(mem["generator"])
        mult = parse_poly(mem["multiplier"])
        acc = padd(acc, pmul(mult, gen))
        h = poly_hash(gen)
        hit = table.get(h)
        if hit:
            matched.append((mem["generator_index_zero_based"], hit[0][0], hit[0][2]))
        else:
            unmatched.append(mem["generator_index_zero_based"])
            unmatched_polys.append((mem["generator_index_zero_based"], gen))
    one = acc == {(): 1}
    return {
        "sum_is_1": one,
        "n_members": len(cert["members"]),
        "unmatched_generator_indices": unmatched,
        "matched_kinds": matched,
        "sum_terms": len(acc),
        **check_unmatched_block_span(unmatched_polys, block_basis),
    }


def replay_circuit(cert, table, grade, block_basis, projection_hashes):
    ogs = [parse_poly(g) for g in cert["original_generators"]]
    # homogeneity of every stored generator that appears, and of used sources
    nonhom = []
    for i, poly in enumerate(ogs):
        # grading may omit z_first; any variable used must be graded.
        # Extend grade with first_label -> 0 if missing.
        ok, degs = is_homogeneous(poly, grade)
        if not ok:
            nonhom.append(i if degs is None else (i, sorted(degs)[:6] if isinstance(degs, set) else degs))
            if len(nonhom) > 8:
                break
    rows = [subs_ty_one(g) for g in ogs]
    step_fail = None
    used_interp = []
    for si, op in enumerate(cert["preprocessing"]["operations"]):
        if op["kind"] != "affine":
            step_fail = {"step": si, "kind": op["kind"]}
            break
        var = var_name_id(op["variable"])
        inv_c = int(op["inverse_coefficient"]) % P
        eq = parse_poly(op["equation"])
        repl = parse_poly(op["replacement"])
        c = inv(inv_c)
        monic = pscale(psub(punit(var), repl), 1)
        expect_eq = pscale(monic, c)
        pivot = int(op["pivot"])
        quots = {int(k): parse_poly(v) for k, v in op["quotients"].items()}
        if rows[pivot] != eq and rows[pivot] != expect_eq and rows[pivot] != monic:
            step_fail = {
                "step": si,
                "reason": "pivot row is not the stored equation",
                "pivot": pivot,
                "var": op["variable"],
            }
            break
        # choose the pivot polynomial that actually clears var
        def clears(pivot_poly):
            for i, row in enumerate(rows):
                if i == pivot:
                    continue
                Q = quots.get(i)
                new = psub(row, pmul(Q, pivot_poly)) if Q is not None else row
                if coeff_of_var(new, var) != 0:
                    return False
            return True

        chosen = None
        for name, pp in (("equation", eq), ("monic", monic), ("c*monic", expect_eq)):
            if clears(pp):
                chosen = (name, pp)
                break
        if chosen is None:
            step_fail = {"step": si, "reason": "no interpretation clears the pivot variable", "var": op["variable"]}
            break
        used_interp.append(chosen[0])
        new_rows = []
        pp = chosen[1]
        for i, row in enumerate(rows):
            if i == pivot:
                new_rows.append({})
                continue
            Q = quots.get(i)
            new_rows.append(psub(row, pmul(Q, pp)) if Q is not None else row)
        rows = new_rows
    acc = {}
    if step_fail is None:
        for rm in cert["reduced_members"]:
            mult = parse_poly(rm["multiplier"])
            acc = padd(acc, pmul(mult, rows[int(rm["row_index_zero_based"])]))
    # match original generators (chart, before t=y=1) against the model
    unmatched = []
    matched_core = 0
    for i, poly in enumerate(ogs):
        hit = table.get(poly_hash(poly))
        if hit:
            matched_core += 1
        else:
            if i < 20 or (3258 <= i < len(ogs)):
                unmatched.append(i)
    # Reconstruct all dependency leaves of the nonzero final multipliers.
    if step_fail is None:
        dep = [{i} for i in range(len(ogs))]
        for op in cert["preprocessing"]["operations"]:
            pivot = int(op["pivot"])
            pdep = dep[pivot]
            for idx, quotient in op["quotients"].items():
                i = int(idx)
                if i != pivot and parse_poly(quotient):
                    dep[i] = dep[i] | pdep
            dep[pivot] = set()
        used = set()
        for rm in cert["reduced_members"]:
            if parse_poly(rm["multiplier"]):
                used |= dep[int(rm["row_index_zero_based"])]
        declared = set(cert.get("source_generator_indices_zero_based") or [])
        missing_leaf = sorted(used - declared)
        extra_leaf = sorted(declared - used)
    else:
        used, missing_leaf, extra_leaf = set(), [], []
    # The legacy sample above includes unused rows and omits middle indices.
    # Authenticate every used leaf, including full character projections and
    # their weight initials, before checking the remaining linear relations.
    unmatched_used = []
    projection_matches = 0
    for i in sorted(used):
        h = poly_hash(ogs[i])
        if h in table:
            continue
        if h in projection_hashes:
            projection_matches += 1
            continue
        unmatched_used.append((i, ogs[i]))
    return {
        "sum_is_1": acc == {(): 1},
        "sum_terms": len(acc),
        "step_fail": step_fail,
        "interp_counts": {k: used_interp.count(k) for k in sorted(set(used_interp))},
        "n_steps": len(cert["preprocessing"]["operations"]),
        "nonhomogeneous_generators_sample": nonhom[:8],
        "n_nonhomogeneous_truncated": len(nonhom),
        "generators_matched_to_model": matched_core,
        "n_generators": len(ogs),
        "unmatched_sample": unmatched[:30],
        "dependency_missing_from_declared": missing_leaf[:40],
        "n_dependency_missing": len(missing_leaf),
        "n_declared_extra_leaves": len(extra_leaf),
        "n_used_leaves": len(used),
        "used_generators_matched_to_model": len(used) - len(unmatched_used),
        "used_generators_matched_to_projections": projection_matches,
        "unmatched_used_generator_indices": [i for i, _ in unmatched_used],
        **check_unmatched_block_span(unmatched_used, block_basis),
    }


def coeff_of_var(poly, var):
    for key, c in poly.items():
        if any(v == var for v, _e in key):
            return 1  # still present
    return 0


def audit_certificates(data_dir, weyl: Weyl):
    status, metas = load_merge_certificates(data_dir)
    results = []
    for meta in metas:
        cert = load_json_gz(data_dir, meta["files"])
        w, mu = parse_weights(cert)
        z_first = int(cert["first_label"])
        info = cert.get("normalization_info") or {}
        A = info.get("A")
        B = info.get("B")
        if A is None:
            results.append({"files": meta["files"], "error": "no rectangle"})
            continue
        grade, q = grades_of(cert)
        grade.setdefault(z_first, 0)
        grade.setdefault(T_VAR, q)
        grade.setdefault(Y_VAR, -q)
        table, parents, prods, trace, ty = index_model(weyl, z_first, A, B, w, mu)
        block_basis = linear_span_basis(block_relation_polys(weyl, A, B, z_first))
        if cert["schema"] == "portable-unit-cell-v1":
            rep = replay_flat(cert, table, block_basis)
        elif cert["schema"] == "portable-unit-circuit-v1":
            projection_hashes = set(projection_chart_hashes(weyl, z_first))
            for poly, _ in projection_chart_items(weyl, z_first):
                init, _ = initial_form(poly, w, mu)
                projection_hashes.add(poly_hash(init))
            rep = replay_circuit(cert, table, grade, block_basis, projection_hashes)
        else:
            rep = {"error": cert["schema"]}
        rep["files"] = meta["files"]
        rep["schema"] = cert["schema"]
        rep["mask"] = meta["mask"]
        rep["orbit_index"] = meta["orbit_index"]
        rep["sha256"] = meta["sha256"]
        # grading versus weights
        bad_grade = []
        for i, wi in enumerate(w):
            if i == z_first:
                continue
            gi = grade.get(i)
            if gi is None:
                continue
            if Fraction(gi, q) != wi:
                bad_grade.append(i)
                if len(bad_grade) > 6:
                    break
        rep["grade_weight_mismatches_sample"] = bad_grade
        results.append(rep)
        print(
            "cert",
            meta["files"][0],
            "sum1" if rep.get("sum_is_1") else "SUM_FAIL",
            "unmatched",
            len(rep.get("unmatched_generator_indices", rep.get("unmatched_used_generator_indices", []))),
            "linear_in_block_span",
            rep.get("unmatched_linear_in_block_span"),
            "unexplained",
            rep.get("unmatched_not_explained"),
            "step",
            rep.get("step_fail"),
            flush=True,
        )
        if rep.get("unmatched_not_explained"):
            print(json.dumps(rep, indent=2, default=str), flush=True)
            raise ValueError("unexplained generators in " + meta["files"][0])
    return {"merge_status_field": status, "n": len(results), "results": results}


def necessary_patterns(weyl: Weyl):
    """Term-sets of ideal members with at least two monomials.

    A one-monomial member is a support constraint, already enforced by the
    census. Encoding it as a weight contradiction would make every cover UNSAT
    for a spurious reason. z0 terms stay: on a trait w(z0)=mu/2, they are real
    terms of the initial-form comparison.
    """
    pats = []

    def absorb(poly):
        for proj in projections_of(poly):
            terms = []
            for key, c in proj.items():
                if c % P == 0:
                    continue
                labs = mon_labels(key)
                if not labs:
                    continue
                terms.append(tuple(sorted(labs)))
            terms = tuple(sorted(set(terms)))
            if len(terms) >= 2:
                pats.append(terms)

    for poly in weyl.minors():
        absorb(poly)
    for poly in weyl.square_polys():
        absorb(poly)
    return sorted(set(pats))


def z3_weight_unsat(mask, patterns, cells, shears, threads=8, timeout_ms=0):
    """cells: list of list of (leader_mons, all_mons) for one block's certificates.
    Returns unsat/sat and a sample point.
    """
    from z3 import And, Not, Or, Real, Solver, sat

    s = Solver()
    s.set("threads", threads)
    s.set("max_memory", 40000)
    if timeout_ms:
        s.set("timeout", timeout_ms)
    w = [Real(f"w{q}") for q in range(49)]
    mu = Real("mu")
    s.add(mu == 1)
    s.add(w[0] * 2 == mu)
    selected = [(mask >> q & 1) == 1 for q in range(49)]
    seen = set()
    for q in range(1, 49):
        o = opp_label(q)
        pair = (q, o) if q < o else (o, q)
        if pair in seen or q == o:
            continue
        seen.add(pair)
        if selected[q]:
            s.add(w[q] == 0, w[o] == mu)
        elif selected[o]:
            s.add(w[o] == 0, w[q] == mu)
        else:
            s.add(w[q] > 0, w[o] > 0, w[q] + w[o] == mu)
    for q in range(49):
        s.add(w[q] >= 0, w[q] <= mu)

    def W(mon, weight_of):
        return sum(weight_of[q] for q in mon)

    def add_necessary(weight_of):
        cons = []
        for pat in patterns:
            # forbid a unique minimum
            ors = []
            for i, mon in enumerate(pat):
                others = [W(pat[j], weight_of) <= W(mon, weight_of) for j in range(len(pat)) if j != i]
                if not others:
                    ors.append(False)
                else:
                    ors.append(Or(others) if len(others) > 1 else others[0])
            # every term has some other term <= it. Encoded per term inside ors; all must hold.
            cons.append(And(ors) if len(ors) > 1 else ors[0])
        return cons

    for cons in add_necessary(w):
        s.add(cons)

    def cell_holds(weight_of, cell):
        bits = []
        for leaders, all_mons in cell:
            leaders = list(leaders)
            if not leaders:
                continue
            non = [m for m in all_mons if m not in set(leaders)]
            for a, b in zip(leaders, leaders[1:]):
                bits.append(W(a, weight_of) == W(b, weight_of))
            for n in non:
                bits.append(W(n, weight_of) > W(leaders[0], weight_of))
        if not bits:
            return False
        return And(bits)

    cover = []
    for cell in cells:
        for perm in shears:
            # The image set is a group, so w_rep[q] = w[perm[q]] and w[perm^{-1} q]
            # sweep the same set of transports.
            pulled = [w[perm[q]] for q in range(49)]
            cover.append(cell_holds(pulled, cell))
    if cover:
        s.add(Not(Or(cover) if len(cover) > 1 else cover[0]))
    t0 = time.time()
    result = s.check()
    dt = time.time() - t0
    sample = None
    if str(result) == "sat":
        model = s.model()
        sample = []
        for q in range(49):
            sample.append(str(model.evaluate(w[q], model_completion=True)))
    return str(result), dt, sample


def weight_image_perms(square):
    """(r,k) -> (r, s*k + c*r). Shears s=1 always. Reflections s=-1 only for the
    two blocks whose rectangle returns to itself after an X correction: the 1x1
    and the 2x2. Those are exactly the families with 14 safe weight images.
    """
    perms = []
    signs = (1, -1) if square else (1,)
    for s in signs:
        for c in range(D):
            perm = [0] * 49
            for r in range(D):
                for k in range(D):
                    perm[r * D + k] = r * D + ((s * k + c * r) % D)
            perms.append(tuple(perm))
    return perms


# kept name used nowhere else; square blocks are selected in audit_weights
def shear_perms():
    return weight_image_perms(False)


def reflect_perm():
    perm = [0] * 49
    for r in range(D):
        for k in range(D):
            perm[r * D + k] = r * D + ((-k) % D)
    return tuple(perm)


def monomial_of_key(key):
    labs = mon_labels(key)
    if labs is None:
        return None
    return tuple(sorted(labs))


def weight_in_cell(weights, cell):
    def W(mon):
        return sum((weights[q] for q in mon), Fraction(0))

    for leaders, all_mons in cell:
        if not leaders:
            return False
        base = W(leaders[0])
        if any(W(m) != base for m in leaders[1:]):
            return False
        leader_set = set(leaders)
        for m in all_mons:
            if m not in leader_set and not (W(m) > base):
                return False
    return True


def drop_unit(mon, z_first):
    return tuple(q for q in mon if q != z_first)


def projection_chart_items(weyl, z_first):
    cache = getattr(weyl, "_proj_chart_items", None)
    if cache is None:
        cache = {}
        weyl._proj_chart_items = cache
    if z_first in cache:
        return cache[z_first]
    items = []
    for poly in weyl.minors() + weyl.square_polys():
        for proj in projections_of(poly):
            ch = subs_one(proj, z_first)
            mons = []
            ok = True
            for key in ch.keys():
                mon = monomial_of_key(key)
                if mon is None:
                    ok = False
                    break
                mons.append(mon)
            if ok:
                items.append((ch, mons))
    cache[z_first] = items
    return items


def projection_parent_candidates(weyl, z_first, G, weights, mu):
    """Chart projections whose initial form at this weight is the printed generator."""
    out = []
    target = poly_hash(G)
    for ch, mons in projection_chart_items(weyl, z_first):
        init, _ = initial_form(ch, weights, mu)
        if poly_hash(init) == target:
            out.append(mons)
    return out


def projection_chart_hashes(weyl, z_first):
    cache = getattr(weyl, "_proj_chart_hashes", None)
    if cache is None:
        cache = {}
        weyl._proj_chart_hashes = cache
    if z_first in cache:
        return cache[z_first]
    hashes = set()
    sources = weyl.minors() + weyl.square_polys()
    for poly in sources:
        for proj in projections_of(poly):
            hashes.add(poly_hash(subs_one(proj, z_first)))
    cache[z_first] = hashes
    return hashes


def build_cells_for_block(data_dir, weyl, metas_for_block):
    """Leader cells from the model polynomial named by the certificate index.

    The printed member is only the initial form, so its own term count is shorter
    than the leader indices. Those indices address the full polynomial in
    construction order. Non-leaders are the other terms of that same polynomial.
    """
    minors = weyl.minors()
    squares = weyl.square_polys()

    def parent(idx):
        if 0 <= idx <= 440:
            return minors[idx]
        if 441 <= idx <= 488:
            return squares[idx - 440]
        return None

    cells = []
    notes = []
    mask = metas_for_block[0]["mask"]
    for meta in metas_for_block:
        cert = load_json_gz(data_dir, meta["files"])
        w, mu = parse_weights(cert)
        z_first = int(cert["first_label"])
        if cert["schema"] == "portable-unit-cell-v1":
            texts = {m["generator_index_zero_based"]: m["generator"] for m in cert["members"]}
        else:
            texts = {i: g for i, g in enumerate(cert["original_generators"])}
        cell = []
        local_notes = []
        for entry in cert["cell"]:
            idx = int(entry["polynomial_index_zero_based"])
            leaders_idx = [int(i) for i in entry["leader_term_indices_zero_based"]]
            poly = parent(idx)
            if poly is None:
                # Projection range. The stored generator is the full chart polynomial
                # when every leader index addresses a printed term. It still has to
                # be a character projection of a minor or a square.
                if idx not in texts:
                    local_notes.append({"idx": idx, "no_parent_index": True})
                    continue
                printed = iter_printed_terms(texts[idx])
                indices_fit = all(0 <= i < len(printed) for i in leaders_idx)
                mons = []
                bad = False
                for key, _c in printed:
                    mon = monomial_of_key(key)
                    if mon is None:
                        bad = True
                        break
                    mons.append(mon)
                if bad:
                    local_notes.append({"idx": idx, "skipped": "contains t or y"})
                    continue
                G = {}
                for key, coeff in printed:
                    s = (G.get(key, 0) + coeff) % P
                    if s:
                        G[key] = s
                    elif key in G:
                        del G[key]
                ph = poly_hash(G)
                proj_hashes = projection_chart_hashes(weyl, z_first)
                if indices_fit and ph in proj_hashes:
                    leaders = tuple(sorted({mons[i] for i in leaders_idx}))
                    all_mons = tuple(sorted(set(mons)))
                    cell.append((leaders, all_mons))
                    continue
                # Printed text is only the initial form. Leader indices address the
                # full projection, whose chart-key order is the construction order.
                unique = []
                for parent_mons in projection_parent_candidates(weyl, z_first, G, w, mu):
                    if any(i < 0 or i >= len(parent_mons) for i in leaders_idx):
                        continue
                    leaders = tuple(sorted({parent_mons[i] for i in leaders_idx}))
                    chart_leaders = {drop_unit(m, z_first) for m in leaders}
                    if set(mons) != chart_leaders:
                        continue
                    cand = (leaders, tuple(sorted(set(parent_mons))))
                    if cand not in unique:
                        unique.append(cand)
                if len(unique) != 1:
                    local_notes.append(
                        {
                            "idx": idx,
                            "projection_parents": len(unique),
                            "nterms": len(G),
                            "nlead": len(leaders_idx),
                        }
                    )
                    continue
                cell.append(unique[0])
                continue
            ordered = []
            bad = False
            for key in poly.keys():
                mon = monomial_of_key(key)
                if mon is None:
                    bad = True
                    break
                ordered.append(mon)
            if bad or any(i < 0 or i >= len(ordered) for i in leaders_idx):
                local_notes.append(
                    {"idx": idx, "index_oob": True, "nterms": len(ordered), "nlead": len(leaders_idx)}
                )
                continue
            leaders = tuple(sorted({ordered[i] for i in leaders_idx}))
            all_mons = tuple(sorted(set(ordered)))
            if idx in texts:
                stated = {monomial_of_key(k) for k, _c in iter_printed_terms(texts[idx])}
                chart_leaders = {drop_unit(m, z_first) for m in leaders}
                if stated != chart_leaders:
                    local_notes.append(
                        {
                            "idx": idx,
                            "leaders_differ_from_printed_generator": True,
                            "n_stated": len(stated),
                            "n_leaders": len(chart_leaders),
                        }
                    )
                    continue
            cell.append((leaders, all_mons))
        own = weight_in_cell(w, cell) if cell else False
        cells.append(cell)
        notes.append(
            {
                "file": meta["files"][0],
                "n_cell_polys": len(cell),
                "n_cell_entries": len(cert["cell"]),
                "certificate_weight_in_cell": own,
                "mu": str(mu),
                "notes": local_notes[:12],
            }
        )
    return mask, cells, notes


def twenty_mask():
    return 267386752


def audit_weights(data_dir, weyl, threads, only_mask=0, timeout_ms=180000, complete_only=False):
    status, metas = load_merge_certificates(data_dir)
    by_block = defaultdict(list)
    for meta in metas:
        if only_mask and meta["mask"] != only_mask:
            continue
        by_block[(meta["mask"], meta["orbit_index"])].append(meta)
    patterns = necessary_patterns(weyl)
    square_keys = {(16256, 0), (268435328, 1)}
    out = []
    for key, group in by_block.items():
        mask, cells, notes = build_cells_for_block(data_dir, weyl, group)
        images = weight_image_perms(key in square_keys)
        if complete_only:
            cells = [c for c, note in zip(cells, notes) if c and not note["notes"]]
        else:
            cells = [c for c in cells if c]
        result, dt, sample = z3_weight_unsat(
            mask, patterns, cells, images, threads=threads, timeout_ms=timeout_ms
        )
        out.append(
            {
                "mask": mask,
                "orbit_index": key[1],
                "n_certificates": len(group),
                "n_cells_used": len(cells),
                "z3": result,
                "seconds": dt,
                "sample": sample,
                "notes": notes,
            }
        )
        print("cover", mask, key[1], result, f"{dt:.1f}s", flush=True)
    # twenty-element, no cells
    if only_mask and only_mask != twenty_mask():
        return {"n_patterns": len(patterns), "blocks": out, "complete_only": complete_only}
    tmask = twenty_mask()
    result, dt, sample = z3_weight_unsat(
        tmask, patterns, [], weight_image_perms(False), threads=threads, timeout_ms=timeout_ms
    )
    out.append(
        {
            "mask": tmask,
            "orbit_index": None,
            "kind": "twenty-element-base",
            "z3": result,
            "seconds": dt,
            "sample_prefix": sample[:8] if sample else None,
        }
    )
    print("cover twenty", result, f"{dt:.1f}s", flush=True)
    return {"n_patterns": len(patterns), "blocks": out}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default=str(public_root(__file__) / "sources/d7-finiteness/numerics"))
    ap.add_argument("--out", default=str(public_root(__file__) / "work/finiteness/out"))
    ap.add_argument("--stage", required=True, choices=["self", "n1", "n2", "n3", "n4", "all"])
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--tau", type=int, default=16)
    ap.add_argument("--only-mask", type=int, default=0)
    ap.add_argument("--timeout-ms", type=int, default=180000)
    ap.add_argument("--complete-only", action="store_true")
    ap.add_argument("--out-name", default="")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    weyl = Weyl(args.tau)
    if args.stage in ("self", "all"):
        rep = self_test(weyl)
        _dump(args.out, "self", rep)
        print(json.dumps(rep, indent=2, default=str))
        if not all(
            rep[k]
            for k in (
                "tau7_is_1",
                "reconstruction_7abT",
                "c_q_equals_Z_minus_q",
                "minors_vanish_on_rank1",
                "squares_vanish_on_rank1",
                "row_witness_C",
                "products_zero_on_row",
                "z0_zero_on_row",
                "parse_ty",
                "parse_prod",
                "parse_trace_is_z0sq_minus_8t",
                "parse_bare_coeff",
                "parse_pow",
            )
        ):
            raise SystemExit("self-test failed")
    if args.stage in ("n1", "all"):
        rep = coefficient_valuations(args.tau)
        _dump(args.out, "n1", rep)
        print("n1 positive", rep["n_positive_at_some_prime"], "of", rep["n_minor_coefficients"])
    if args.stage in ("n2", "all"):
        rep = support_census(weyl, args.threads)
        _dump(args.out, "n2", rep)
        print(
            "n2 group",
            rep["group_conjugation_order"],
            "closed",
            rep["closed_patterns"],
            "z3",
            rep["z3_closed_outside_claimed"],
            "claimed",
            rep["claimed_blocked"],
        )
    if args.stage in ("n3", "all"):
        rep = audit_certificates(args.data, weyl)
        _dump(args.out, "n3", rep)
    if args.stage in ("n4", "all"):
        rep = audit_weights(
            args.data,
            weyl,
            args.threads,
            only_mask=args.only_mask,
            timeout_ms=args.timeout_ms,
            complete_only=args.complete_only,
        )
        _dump(args.out, args.out_name or "n4", rep)


def _dump(out, name, obj):
    path = os.path.join(out, name + ".json")
    with open(path, "w") as f:
        json.dump(obj, f, indent=2, default=str)
    print("wrote", path, flush=True)


if __name__ == "__main__":
    main()
