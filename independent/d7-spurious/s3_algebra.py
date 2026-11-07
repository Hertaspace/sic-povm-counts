#!/usr/bin/env python3
"""Exact algebraic checks for the d=7 q-map, M0, and the order-98 group.

Cyclotomic arithmetic is integer tuples modulo Phi_7. No certificate roots
are read. Matrix numerators are read from e40_d7_matrix.json only.
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
import random
from fractions import Fraction as Q
from pathlib import Path

D = 7
NUM = public_root(__file__) / "sources/d7/numerics" / "e40_d7_matrix.json"
OUT = public_root(__file__) / "independent/d7-spurious/out" / "s3_algebra.json"

# basis 1, w, ..., w^5 with w^6 = -1-w-...-w^5, w^7 = 1


def cred(cs):
    a = [Q(0)] * 6
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


def cmul(u, v):
    raw = [Q(0)] * 12
    for i, a in enumerate(u):
        if a == 0:
            continue
        for j, b in enumerate(v):
            if b:
                raw[i + j] += a * b
    return cred(raw)


def cadd(u, v):
    return tuple(u[i] + v[i] for i in range(6))


def csub(u, v):
    return tuple(u[i] - v[i] for i in range(6))


def cneg(u):
    return tuple(-x for x in u)


def cscale(u, q):
    return tuple(x * q for x in u)


ZERO = (Q(0),) * 6
ONE = (Q(1), Q(0), Q(0), Q(0), Q(0), Q(0))


def wpow(e):
    e %= 7
    if e == 0:
        return ONE
    if e < 6:
        xs = [Q(0)] * 6
        xs[e] = Q(1)
        return tuple(xs)
    return cneg(cadd(ONE, cred([Q(0), Q(1), Q(1), Q(1), Q(1), Q(1)])))  # w^6


# monomial: tuple of 14 exponents (a0..a6, b0..b6) -> Cyc


def pmul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(e1[i] + e2[i] for i in range(14))
            coef = cmul(c1, c2)
            if any(coef):
                out[e] = cadd(out.get(e, ZERO), coef)
    return {e: c for e, c in out.items() if any(c)}


def padd(p, q):
    out = dict(p)
    for e, c in q.items():
        out[e] = cadd(out.get(e, ZERO), c)
        if not any(out[e]):
            del out[e]
    return out


def pscale(p, c):
    return {e: cmul(v, c) for e, v in p.items() if any(cmul(v, c))}


def var(idx):
    e = [0] * 14
    e[idx] = 1
    return {tuple(e): ONE}


def q_poly(a, b):
    """a, b: lists of 7 polynomials. Return 24 q polynomials in lex-rep order."""
    labels = lex_reps()
    qs = []
    for i, j in labels:
        S = {}
        U = {}
        V = {}
        for k in range(7):
            S = padd(S, pmul(a[k], b[k]))
            wk = wpow(j * k)
            wmk = wpow((-j * k) % 7)
            U = padd(U, pscale(pmul(a[k], b[(k + i) % 7]), wk))
            V = padd(V, pscale(pmul(a[k], b[(k - i) % 7]), wmk))
        wij = wpow(i * j)
        term = pscale(pmul(U, V), wij)
        S2 = pmul(S, S)
        # minus S^2/8
        qs.append(padd(term, pscale(S2, cscale(ONE, Q(-1, 8)))))
    return qs


def lex_reps():
    seen = set()
    reps = []
    for i in range(7):
        for j in range(7):
            if (i, j) == (0, 0):
                continue
            rep = min((i, j), ((-i) % 7, (-j) % 7))
            if rep not in seen:
                seen.add(rep)
                reps.append(rep)
    return sorted(reps)


def standard_ab():
    a = [var(k) for k in range(7)]
    b = [var(7 + k) for k in range(7)]
    return a, b


def apply_op(a, b, i, j, s):
    """(Ua)_k = w^{j k} a_{s(k-i)}, (U^{-T}b)_k = w^{-j k} b_{s(k-i)}."""
    na = []
    nb = []
    for k in range(7):
        ia = (s * (k - i)) % 7
        na.append(pscale(a[ia], wpow(j * k)))
        nb.append(pscale(b[ia], wpow((-j * k) % 7)))
    return na, nb


def group_labels():
    return [(s, i, j) for s in (1, -1) for i in range(7) for j in range(7)]


def cyc_is_scalar_matrix(rows):
    """rows: 7 vectors in Q(w)^7. True if a scalar multiple of I, including 0."""
    # find a nonzero diagonal candidate
    lam = None
    for r in range(7):
        for c in range(7):
            val = rows[r][c]
            if r != c and any(val):
                return False
        if lam is None and any(rows[r][r]):
            lam = rows[r][r]
        elif lam is not None and rows[r][r] != lam:
            return False
    return True


def mat_mul(A, B):
    n = 7
    C = [[ZERO for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if not any(A[i][k]):
                continue
            for j in range(n):
                if any(B[k][j]):
                    C[i][j] = cadd(C[i][j], cmul(A[i][k], B[k][j]))
    return C


def mat_vec_on_basis(i, j, s):
    """Columns are images of e_0..e_6."""
    cols = []
    for t in range(7):
        # U e_t has component k equal to w^{jk} if s(k-i) == t, else 0
        col = [ZERO] * 7
        for k in range(7):
            if (s * (k - i)) % 7 == t:
                col[k] = wpow(j * k)
        cols.append(col)
    # return as rows
    return [[cols[c][r] for c in range(7)] for r in range(7)]


def gaussian_rank(rows):
    """rows: list of dicts monomial->Cyc. Exact rank over Q(w)."""
    keys = sorted({e for row in rows for e in row})
    index = {e: t for t, e in enumerate(keys)}
    # matrix of Cyc, shape n x m
    n = len(rows)
    m = len(keys)
    M = [[ZERO for _ in range(m)] for _ in range(n)]
    for r, row in enumerate(rows):
        for e, c in row.items():
            M[r][index[e]] = c
    rank = 0
    col = 0
    used = [False] * n
    while col < m and rank < n:
        piv = None
        for r in range(n):
            if not used[r] and any(M[r][col]):
                piv = r
                break
        if piv is None:
            col += 1
            continue
        used[piv] = True
        rank += 1
        inv = cinv(M[piv][col])
        for r in range(n):
            if r == piv or not any(M[r][col]):
                continue
            f = cmul(M[r][col], inv)
            for c in range(col, m):
                M[r][c] = csub(M[r][c], cmul(f, M[piv][c]))
        col += 1
    return rank, m


def cinv(u):
    # inverse in Q(w) via linear algebra on the basis
    # solve u * x = 1
    A = []
    for k in range(6):
        ek = [Q(0)] * 6
        ek[k] = Q(1)
        prod = cmul(u, tuple(ek))
        A.append(list(prod))
    # A is columns of multiplication-by-u. Solve A^T? prod basis coeffs are rows if
    # cmul returns coordinates. Build matrix whose columns are u*e_k.
    M = [[Q(0)] * 6 for _ in range(6)]
    for k in range(6):
        ek = [Q(0)] * 6
        ek[k] = Q(1)
        prod = cmul(u, tuple(ek))
        for r in range(6):
            M[r][k] = prod[r]
    b = [Q(1)] + [Q(0)] * 5
    # gaussian elimination
    A = [M[r][:] + [b[r]] for r in range(6)]
    for col in range(6):
        piv = None
        for r in range(col, 6):
            if A[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ZeroDivisionError("noninvertible cyclotomic")
        A[col], A[piv] = A[piv], A[col]
        div = A[col][col]
        A[col] = [x / div for x in A[col]]
        for r in range(6):
            if r == col or A[r][col] == 0:
                continue
            f = A[r][col]
            A[r] = [A[r][j] - f * A[col][j] for j in range(7)]
    return tuple(A[r][6] for r in range(6))


def rank_over_gaussian(Mre, Mim):
    """12 x 24 matrix over Q(i). Return rank."""
    n, m = 12, 24
    # entries (re, im) Fractions
    A = [[(Q(Mre[r][c]), Q(Mim[r][c])) for c in range(m)] for r in range(n)]

    def add(u, v):
        return (u[0] + v[0], u[1] + v[1])

    def sub(u, v):
        return (u[0] - v[0], u[1] - v[1])

    def mul(u, v):
        return (u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0])

    def inv(u):
        d = u[0] * u[0] + u[1] * u[1]
        return (u[0] / d, -u[1] / d)

    def is0(u):
        return u == (Q(0), Q(0))

    rank = 0
    col = 0
    used = [False] * n
    while col < m and rank < n:
        piv = None
        for r in range(n):
            if not used[r] and not is0(A[r][col]):
                piv = r
                break
        if piv is None:
            col += 1
            continue
        used[piv] = True
        rank += 1
        iv = inv(A[piv][col])
        for r in range(n):
            if r == piv or is0(A[r][col]):
                continue
            f = mul(A[r][col], iv)
            for c in range(col, m):
                A[r][c] = sub(A[r][c], mul(f, A[piv][c]))
        col += 1
    return rank


def header_formula_poly(a, b):
    """Proposer's header transcription, to compare with b^T D a product."""
    labels = lex_reps()
    qs = []
    for i, j in labels:
        S = {}
        left = {}
        right = {}
        phase = wpow((-i * j) % 7)
        for k in range(7):
            S = padd(S, pmul(a[k], b[k]))
            left = padd(left, pscale(pmul(b[k], a[(k - i) % 7]), wpow(j * k)))
            right = padd(right, pscale(pmul(b[k], a[(k + i) % 7]), wpow((-j * k) % 7)))
        term = pscale(pmul(left, right), phase)
        qs.append(padd(term, pscale(pmul(S, S), cscale(ONE, Q(-1, 8)))))
    return qs


def main():
    random.seed(20261102)
    labels = lex_reps()
    assert len(labels) == 24
    a, b = standard_ab()
    print("building base q", flush=True)
    base = q_poly(a, b)
    alt = header_formula_poly(a, b)
    header_match = all(base[t] == alt[t] for t in range(24))
    print("header formula match", header_match, flush=True)

    # dropping the omega^{ij} phase changes the polynomial
    bare = []
    for t, (i, j) in enumerate(labels):
        # base = w^{ij} UV - S^2/8; bare replaces w^{ij} by 1, difference (w^{ij}-1)UV
        bare.append(i * j % 7 != 0)
    phase_nontrivial = any(bare)
    # explicit difference nonzero for (1,1)
    i = labels.index((1, 1))
    # reconstruct UV from base by... just compare q with phase 1 vs phase w
    a2, b2 = standard_ab()
    # manual (1,1)
    S = {}
    U = {}
    V = {}
    for k in range(7):
        S = padd(S, pmul(a2[k], b2[k]))
        U = padd(U, pscale(pmul(a2[k], b2[(k + 1) % 7]), wpow(k)))
        V = padd(V, pscale(pmul(a2[k], b2[(k - 1) % 7]), wpow((-k) % 7)))
    with_phase = padd(pscale(pmul(U, V), wpow(1)), pscale(pmul(S, S), cscale(ONE, Q(-1, 8))))
    no_phase = padd(pmul(U, V), pscale(pmul(S, S), cscale(ONE, Q(-1, 8))))
    phase_matters = with_phase != no_phase

    print("checking generators and all 98 labels", flush=True)
    preserved = 0
    failed = []
    distinct_ops = []
    for s, i, j in group_labels():
        na, nb = apply_op(a, b, i, j, s)
        qq = q_poly(na, nb)
        ok = all(qq[t] == base[t] for t in range(24))
        if ok:
            preserved += 1
        else:
            failed.append((s, i, j))
        distinct_ops.append(mat_vec_on_basis(i, j, s))
    print("preserved", preserved, "failed", failed[:5], flush=True)

    # projective distinctness: U_a^{-1} U_b is scalar only when labels match
    # Compare canonical: two ops equal projectively iff columns are proportional
    # with one common scalar. Check all pairs via the image of e_0 and a second basis vector.
    def signature(rows):
        # first nonzero column, scaled so its first nonzero entry is 1; plus the
        # scalar relating column 0 and the operator on e_1 after that normalization.
        # Store normalized columns.
        cols = [[rows[r][c] for r in range(7)] for c in range(7)]
        lam = None
        for c in range(7):
            for r in range(7):
                if any(cols[c][r]):
                    lam = cols[c][r]
                    break
            if lam is not None:
                break
        inv = cinv(lam)
        norm = tuple(tuple(cmul(rows[r][c], inv) for c in range(7)) for r in range(7))
        return norm

    sigs = [signature(op) for op in distinct_ops]
    unique_sigs = len(set(sigs))
    print("distinct projective ops", unique_sigs, flush=True)

    # only identity label acts as a scalar
    scalar_labels = []
    for (s, i, j), op in zip(group_labels(), distinct_ops):
        if cyc_is_scalar_matrix(op):
            scalar_labels.append((s, i, j))
    print("scalar labels", scalar_labels, flush=True)

    print("rank of 24 q", flush=True)
    rank, nmon = gaussian_rank(base)
    print("rank", rank, "monomials", nmon, flush=True)

    obj = json.loads(NUM.read_text())
    file_labels = [tuple(p) for p in obj["q_labels"]]
    m_rank = rank_over_gaussian(obj["real_numerators"], obj["imag_numerators"])
    print("M rank", m_rank, flush=True)

    # multiplication law spot-check: compose two random labels and compare matrices up to scalar
    def compose_labels(g, h):
        s, i, j = g
        sp, ip, jp = h
        # U_g U_h = w^{-s i jp} U_{i + s ip, j + s jp, s sp}
        phase = wpow((-s * i * jp) % 7)
        dest = (s * sp, (i + s * ip) % 7, (j + s * jp) % 7)
        return phase, dest

    law_fail = 0
    rng = random.Random(20261102)
    pairs = [(rng.randrange(98), rng.randrange(98)) for _ in range(200)]
    # also all generator products
    gens = [(1, 1, 0), (1, 0, 1), (-1, 0, 0)]
    for gi in range(98):
        for gj in gens:
            pass
    label_index = {lab: t for t, lab in enumerate(group_labels())}
    for ia, ib in pairs:
        g = group_labels()[ia]
        h = group_labels()[ib]
        phase, dest = compose_labels(g, h)
        prod = mat_mul(distinct_ops[ia], distinct_ops[ib])
        target = distinct_ops[label_index[dest]]
        scaled = [[cmul(target[r][c], phase) for c in range(7)] for r in range(7)]
        if prod != scaled:
            law_fail += 1
    # full check on generators × all, cheap enough: 3*98
    for g in gens:
        ia = label_index[g]
        for ib, h in enumerate(group_labels()):
            phase, dest = compose_labels(g, h)
            prod = mat_mul(distinct_ops[ia], distinct_ops[ib])
            target = distinct_ops[label_index[dest]]
            scaled = [[cmul(target[r][c], phase) for c in range(7)] for r in range(7)]
            if prod != scaled:
                law_fail += 1
            phase2, dest2 = compose_labels(h, g)
            prod2 = mat_mul(distinct_ops[ib], distinct_ops[ia])
            target2 = distinct_ops[label_index[dest2]]
            scaled2 = [[cmul(target2[r][c], phase2) for c in range(7)] for r in range(7)]
            if prod2 != scaled2:
                law_fail += 1

    report = {
        "n_labels": len(labels),
        "labels_match_e40": file_labels == labels,
        "header_q_formula_matches_UV": header_match,
        "phase_changes_q_11": phase_matters,
        "q_preserved_by_all_98": preserved == 98 and not failed,
        "n_preserved": preserved,
        "failed_labels": failed,
        "distinct_projective_ops": unique_sigs,
        "scalar_labels": scalar_labels,
        "q_rank": rank,
        "q_monomials_used": nmon,
        "M_rank_over_Q_i": m_rank,
        "multiplication_law_failures": law_fail,
        "denominator": int(obj["denominator"]),
        "chart": obj["chart"],
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
