#!/usr/bin/env python3
"""Independent d=7 spur-root checker.

Reads only root centers and the Gaussian-rational matrix numerators.
Does not use certificate inverses, radii, or freeness witnesses.

Arithmetic: outward-rounded dyadic intervals (gmpy2), not Arb and not
the proposer's 384-bit Python replay. Roots of unity come from the real
cubic of 2*cos(2*pi/7), not from a complex Phi_7 ball supplied by them.
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
import json
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import gmpy2
from gmpy2 import mpz

PREC = 256  # dyadic scale: value = integer * 2^{-PREC}; centers are stored at 2^{-224}
D = 7
NVAR = 12
ONE_S = mpz(1) << PREC
ZERO = mpz(0)

NUMDIR = public_root(__file__) / "sources/d7/numerics"
OUTDIR = public_root(__file__) / "independent/d7-spurious/out"


def shr_down(x, s):
    if s <= 0:
        return x << (-s) if s < 0 else x
    if x >= 0:
        return x >> s
    return -(((-x) + (mpz(1) << s) - 1) >> s)


def shr_up(x, s):
    if s <= 0:
        return x << (-s) if s < 0 else x
    if x >= 0:
        return (x + (mpz(1) << s) - 1) >> s
    return -((-x) >> s)


def rnd_shift(x, s):
    """Round x * 2^{-s} to nearest, ties away from zero."""
    if s <= 0:
        return x << (-s)
    half = mpz(1) << (s - 1)
    if x >= 0:
        return (x + half) >> s
    return -(((-x) + half) >> s)


def iadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def isub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def ineg(a):
    return (-a[1], -a[0])


def imul(a, b):
    prods = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    lo = prods[0]
    hi = prods[0]
    for p in prods[1:]:
        if p < lo:
            lo = p
        elif p > hi:
            hi = p
    return (shr_down(lo, PREC), shr_up(hi, PREC))


def iabs_upper(a):
    """Upper bound of |interval|, as a nonnegative mpz at scale PREC."""
    lo, hi = a
    if hi < 0:
        return -lo
    if lo > 0:
        return hi
    return -lo if -lo > hi else hi


def contains_zero(a):
    return a[0] <= 0 <= a[1]


def mid_iv(a):
    return rnd_shift(a[0] + a[1], 1)


def cadd(z, w):
    return (iadd(z[0], w[0]), iadd(z[1], w[1]))


def csub(z, w):
    return (isub(z[0], w[0]), isub(z[1], w[1]))


def cmul(z, w):
    a, b = z
    c, d = w
    return (isub(imul(a, c), imul(b, d)), iadd(imul(a, d), imul(b, c)))


def cneg(z):
    return (ineg(z[0]), ineg(z[1]))


def cconj(z):
    return (z[0], ineg(z[1]))


def point(re, im=0):
    return ((mpz(re), mpz(re)), (mpz(im), mpz(im)))


def czero():
    return ( (ZERO, ZERO), (ZERO, ZERO) )


def cone():
    return point(ONE_S, ZERO)


# ---------- omega ----------

def certify_omega():
    """Unique root of eta^3+eta^2-2*eta-1 in (1, 2) is 2*cos(2*pi/7).

    p'(eta)=3*eta^2+2*eta-2. Its positive critical point is (-1+sqrt(7))/3.
    sqrt(7)<3, so that point is <2/3<1. p'(1)=3>0, hence p is increasing on
    [1, 2] and the root there is simple and unique. The three real roots are
    2*cos(2*pi/7), 2*cos(4*pi/7), 2*cos(6*pi/7). Only the first lies in (1, 2),
    because 2*pi/7 < pi/2 < 4*pi/7. Positive square root of 1-cos^2 is sin.
    """
    def p_scaled(n):
        # p(n/2^PREC) * 2^{3 PREC}
        return (
            n * n * n
            + ((n * n) << PREC)
            - (n << (2 * PREC + 1))
            - (mpz(1) << (3 * PREC))
        )

    lo = mpz(1) << PREC
    hi = mpz(2) << PREC
    assert p_scaled(lo) < 0 < p_scaled(hi)
    while hi - lo > 1:
        mid = (lo + hi) >> 1
        if p_scaled(mid) <= 0:
            lo = mid
        else:
            hi = mid
    assert p_scaled(lo) <= 0 <= p_scaled(hi)
    # eta in [lo, hi] / 2^PREC, width one ulp
    cos = (lo >> 1, (hi + 1) >> 1)  # /2 outward
    # cos^2
    cos2 = imul(cos, cos)
    one = (ONE_S, ONE_S)
    s2 = isub(one, cos2)
    assert s2[0] > 0
    # sqrt outward of s2
    # sqrt(n/2^PREC) = sqrt(n)/2^{PREC/2}; PREC even
    assert PREC % 2 == 0
    half = PREC // 2
    def isqrt_up(n):
        r = gmpy2.isqrt(n)
        return r if r * r == n else r + 1
    slo = gmpy2.isqrt(s2[0])
    shi = isqrt_up(s2[1])
    sin = (slo << half, shi << half)
    assert sin[0] > 0 and cos[0] > 0
    omega = (cos, sin)
    # powers 0..6 by multiplication; true powers because the true root satisfies them
    wpow = [cone()]
    for _ in range(6):
        wpow.append(cmul(wpow[-1], omega))
    return omega, wpow


# ---------- labels, matrix, jets ----------

def lex_representatives():
    seen = set()
    reps = []
    for i in range(D):
        for j in range(D):
            if i == 0 and j == 0:
                continue
            rep = min((i, j), ((-i) % D, (-j) % D))
            if rep not in seen:
                seen.add(rep)
                reps.append(rep)
    reps.sort()
    if len(reps) != 24:
        raise SystemExit(f"expected 24 pair representatives, got {len(reps)}")
    return reps


def load_matrix():
    obj = json.loads((NUMDIR / "e40_d7_matrix.json").read_text())
    if obj["d"] != 7 or obj["n"] != 12 or obj["m"] != 24:
        raise SystemExit("matrix shape is not 12x24 for d=7")
    if int(obj["denominator"]) != 2**32:
        raise SystemExit("denominator is not 2^32")
    labels = [tuple(p) for p in obj["q_labels"]]
    mine = lex_representatives()
    if labels != mine:
        raise SystemExit(f"matrix label order != lex-first pair reps\nfile={labels}\nmine={mine}")
    if obj["variable_order"] != [
        "a1", "a2", "a3", "a4", "a5", "a6", "b0", "b2", "b3", "b4", "b5", "b6"
    ]:
        raise SystemExit("unexpected variable order")
    shift = PREC - 32
    if shift < 0:
        raise SystemExit("PREC below matrix scale")
    rows = []
    for r in range(12):
        row = []
        for c in range(24):
            re = mpz(obj["real_numerators"][r][c]) << shift
            im = mpz(obj["imag_numerators"][r][c]) << shift
            row.append(point(re, im))
        rows.append(row)
    # header cross-check of numerators, still not using its inverse data
    header = json.loads((NUMDIR / "e41_d7_header.json").read_text())
    if header["M"]["scale"] != -32:
        raise SystemExit("header matrix scale is not -32")
    if [tuple(p) for p in header["q_labels"]] != labels:
        raise SystemExit("header labels differ from e40")
    for r in range(12):
        for c in range(24):
            hr, hi = header["M"]["rows"][r][c]
            if int(hr) != int(obj["real_numerators"][r][c]) or int(hi) != int(obj["imag_numerators"][r][c]):
                raise SystemExit(f"header/e40 numerator mismatch at {(r, c)}")
    return rows, labels


class World:
    def __init__(self):
        self.omega, self.wpow = certify_omega()
        self.M, self.labels = load_matrix()
        self.w_at = self.wpow  # index by exponent mod 7


WORLD = None


def jet_const(z):
    return [z] + [czero() for _ in range(NVAR)]


def jet_var(index, z):
    j = jet_const(z)
    j[1 + index] = cone()
    return j


def jadd(x, y):
    return [cadd(x[k], y[k]) for k in range(NVAR + 1)]


def jsub(x, y):
    return [csub(x[k], y[k]) for k in range(NVAR + 1)]


def jmul(x, y):
    out = [cmul(x[0], y[0])]
    x0 = x[0]
    y0 = y[0]
    for k in range(1, NVAR + 1):
        out.append(cadd(cmul(x0, y[k]), cmul(x[k], y0)))
    return out


def jscale(x, z):
    """Multiply jet by a constant complex interval."""
    return [cmul(x[k], z) for k in range(NVAR + 1)]


def pack(v):
    """v: 12 jets. Return a[7], b[7] jets in the chart a0=b1=1."""
    one = jet_const(cone())
    a = [None] * 7
    b = [None] * 7
    a[0] = one
    b[1] = one
    for i in range(6):
        a[i + 1] = v[i]
    b[0] = v[6]
    for i in range(5):
        b[i + 2] = v[7 + i]
    return a, b


def eval_system(v):
    """Return q[24], F[12], J[12][12], all complex intervals. v is 12 jets."""
    a, b = pack(v)
    wpow = WORLD.w_at
    qs = []
    for i, j in WORLD.labels:
        S = jet_const(czero())
        U = jet_const(czero())
        V = jet_const(czero())
        wij = wpow[(i * j) % 7]
        for k in range(7):
            S = jadd(S, jmul(a[k], b[k]))
            wk = wpow[(j * k) % 7]
            wmk = cconj(wk)
            U = jadd(U, jmul(jmul(a[k], b[(k + i) % 7]), jet_const(wk)))
            V = jadd(V, jmul(jmul(a[k], b[(k - i) % 7]), jet_const(wmk)))
        prod = jmul(U, V)
        prod = jscale(prod, wij)
        S2 = jmul(S, S)
        # S^2/8 = S^2 * 2^{-3}. Values are already at scale PREC; dividing the
        # encoded integer by 8 is an exact shift of a dyadic, done outward.
        q = jsub(prod, _div8(S2))
        qs.append(q)
    # F = M q, J = M * dq
    F = []
    J = []
    for r in range(12):
        acc = czero()
        dacc = [czero() for _ in range(NVAR)]
        row = WORLD.M[r]
        for c in range(24):
            acc = cadd(acc, cmul(row[c], qs[c][0]))
            mc = row[c]
            for t in range(NVAR):
                dacc[t] = cadd(dacc[t], cmul(mc, qs[c][1 + t]))
        F.append(acc)
        J.append(dacc)
    qvals = [q[0] for q in qs]
    return qvals, F, J


def _div8(jet):
    out = []
    for z in jet:
        re = (shr_down(z[0][0], 3), shr_up(z[0][1], 3))
        im = (shr_down(z[1][0], 3), shr_up(z[1][1], 3))
        out.append((re, im))
    return out


def jets_from_center(center, radius):
    """center: list of 12 point-complex (re_mpz, im_mpz). radius mpz at scale PREC."""
    vs = []
    for t, (re, im) in enumerate(center):
        z = ((re - radius, re + radius), (im - radius, im + radius))
        vs.append(jet_var(t, z))
    return vs


def point_jets(center):
    vs = []
    for t, (re, im) in enumerate(center):
        vs.append(jet_var(t, point(re, im)))
    return vs


# ---------- linear algebra on midpoints ----------

def mid_c(z):
    return (mid_iv(z[0]), mid_iv(z[1]))


def pt_add(z, w):
    return (z[0] + w[0], z[1] + w[1])


def pt_sub(z, w):
    return (z[0] - w[0], z[1] - w[1])


def pt_mul(z, w):
    re = z[0] * w[0] - z[1] * w[1]
    im = z[0] * w[1] + z[1] * w[0]
    return (rnd_shift(re, PREC), rnd_shift(im, PREC))


def pt_div(z, w):
    den = w[0] * w[0] + w[1] * w[1]
    if den == 0:
        raise ZeroDivisionError
    re = z[0] * w[0] + z[1] * w[1]
    im = z[1] * w[0] - z[0] * w[1]
    # re, im, den are at scale 2*PREC, so re/den is the exact quotient.
    # Store it at scale PREC: round(re/den * 2^PREC).
    return (
        rnd_nearest_div(re << PREC, den),
        rnd_nearest_div(im << PREC, den),
    )


def rnd_nearest_div(num, den):
    if den < 0:
        num = -num
        den = -den
    half = den >> 1
    if num >= 0:
        return (num + half) // den
    return -(((-num) + half) // den)


def invert_mid(J):
    """Invert 12x12 complex midpoint matrix. Returns point matrix A."""
    n = 12
    A = [[mid_c(J[i][j]) for j in range(n)] for i in range(n)]
    eye = (ONE_S, ZERO)
    zero = (ZERO, ZERO)
    M = [row + [eye if i == j else zero for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = col
        best = M[col][col][0] * M[col][col][0] + M[col][col][1] * M[col][col][1]
        for r in range(col + 1, n):
            mag = M[r][col][0] * M[r][col][0] + M[r][col][1] * M[r][col][1]
            if mag > best:
                best = mag
                piv = r
        if best == 0:
            raise ZeroDivisionError("singular midpoint Jacobian")
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
        pivv = M[col][col]
        for j in range(col, 2 * n):
            M[col][j] = pt_div(M[col][j], pivv)
        for r in range(n):
            if r == col:
                continue
            f = M[r][col]
            if f == (ZERO, ZERO):
                continue
            for j in range(col, 2 * n):
                M[r][j] = pt_sub(M[r][j], pt_mul(f, M[col][j]))
    return [row[n:] for row in M]


def apply_A_F(A, F):
    out = []
    for i in range(12):
        acc = czero()
        for j in range(12):
            acc = cadd(acc, cmul(point(A[i][j][0], A[i][j][1]), F[j]))
        out.append(acc)
    return out


def apply_A_J(A, J):
    """A is point matrix, J is interval matrix. Return B = I - A J."""
    n = 12
    AJ = []
    for i in range(n):
        row = []
        for j in range(n):
            acc = czero()
            for k in range(n):
                acc = cadd(acc, cmul(point(A[i][k][0], A[i][k][1]), J[k][j]))
            row.append(acc)
        AJ.append(row)
    B = []
    for i in range(n):
        row = []
        for j in range(n):
            zij = AJ[i][j]
            if i == j:
                # 1 - AJ_ij
                re = isub((ONE_S, ONE_S), zij[0])
                im = ineg(zij[1])
                row.append((re, im))
            else:
                row.append(cneg(zij))
        B.append(row)
    return B


def rho_sum(B):
    """Max over rows of sum_j (sup|Re|+sup|Im|), as mpz at scale PREC."""
    best = ZERO
    for i in range(12):
        s = ZERO
        for j in range(12):
            s += iabs_upper(B[i][j][0]) + iabs_upper(B[i][j][1])
        if s > best:
            best = s
    return best


def eta_of(AF):
    best = ZERO
    for z in AF:
        for part in z:
            u = iabs_upper(part)
            if u > best:
                best = u
    return best


def krawczyk(center, radius):
    vs = jets_from_center(center, radius)
    _q, F, J = eval_system(vs)
    # AF(c): evaluate F at the center point, not on the whole box.
    # The contraction proof uses AF(c) and J on the box.
    _q0, F0, _J0 = eval_system(point_jets(center))
    Jmid_for_A = _J0
    A = invert_mid(Jmid_for_A)
    AF = apply_A_F(A, F0)
    B = apply_A_J(A, J)
    rho = rho_sum(B)          # / 2^PREC
    eta = eta_of(AF)          # / 2^PREC
    R = radius                # / 2^PREC
    scale = mpz(1) << PREC
    # rho < 1 and eta + rho * r < r
    ok_rho = rho < scale
    # eta * scale + rho * R < R * scale
    ok_incl = eta * scale + rho * R < R * scale
    return ok_rho and ok_incl, {
        "rho": int(rho),
        "eta": int(eta),
        "radius": int(R),
        "q": _q,
        "F0": F0,
    }


def newton_refine(center, steps=3):
    x = [(re, im) for re, im in center]
    log_steps = []
    for _ in range(steps):
        _q, F, J = eval_system(point_jets(x))
        A = invert_mid(J)
        # delta = A F, point-rounded
        delta = []
        max_abs = ZERO
        for i in range(12):
            re = ZERO
            im = ZERO
            for j in range(12):
                # point mul of A_ij and midpoint of F_j
                fj = mid_c(F[j])
                pr = pt_mul(A[i][j], fj)
                re += pr[0]
                im += pr[1]
            delta.append((re, im))
            if abs(re) > max_abs:
                max_abs = abs(re)
            if abs(im) > max_abs:
                max_abs = abs(im)
        log_steps.append(int(max_abs))
        x = [(x[i][0] - delta[i][0], x[i][1] - delta[i][1]) for i in range(12)]
        if max_abs == 0:
            break
    return x, log_steps


def moved(a, b):
    m = ZERO
    for (ar, ai), (br, bi) in zip(a, b):
        m = max(m, abs(ar - br), abs(ai - bi))
    return int(m)


def rect_excludes_zero(z):
    return (not contains_zero(z[0])) or (not contains_zero(z[1]))


def group_elements():
    out = []
    for s in (1, -1):
        for i in range(D):
            for j in range(D):
                if s == 1 and i == 0 and j == 0:
                    continue
                out.append((s, i, j))
    if len(out) != 97:
        raise RuntimeError(len(out))
    return out


ELEMS = group_elements()


def coord_interval(a_jets_vals, k):
    """a_jets_vals is a list of 7 complex intervals, index k mod 7. Not used."""
    raise RuntimeError


def stabilizer_ok(center, radius):
    """Cross product on the a-side. a0 = 1 exactly. Box intervals for the free a's."""
    # build a[7] complex intervals
    a = [None] * 7
    a[0] = cone()
    for i in range(6):
        re, im = center[i]
        a[i + 1] = ((re - radius, re + radius), (im - radius, im + radius))
    wpow = WORLD.w_at
    for s, i, j in ELEMS:
        good = False
        for k in range(1, 7):
            # Delta = ω^{j k} a_{s(k-i)} - a_k a_{s(-i)}
            wk = wpow[(j * k) % 7]
            left_index = (s * (k - i)) % 7
            right_index = (s * (-i)) % 7
            left = cmul(wk, a[left_index])
            right = cmul(a[k], a[right_index])
            delta = csub(left, right)
            if rect_excludes_zero(delta):
                good = True
                break
        if not good:
            return False
    return True


def ratio_interval(num, den):
    """(re, im) / (re, im), outward. den rectangle must exclude 0."""
    a, b = num
    c, d = den
    # (a+bi)(c-di) / (c^2+d^2)
    conj_den = (c, ineg(d))
    numer = cmul((a, b), conj_den)
    cc = imul(c, c)
    dd = imul(d, d)
    nrm = iadd(cc, dd)
    if contains_zero(nrm):
        return None
    def idiv(x, y):
        # x/y with y not containing 0, outward, result at scale PREC
        # x, y at scale PREC. x/y = (x_int/y_int).
        # result_int ≈ x_int/y_int * 2^0? both scale PREC so quotient is unscaled
        # number, and we want result_int / 2^PREC = x_int/y_int
        # result_int = x_int * 2^PREC / y_int, outward over the endpoint rectangle.
        # y > 0 or y < 0 entirely.
        cands_lo = []
        cands_hi = []
        for xn in (x[0], x[1]):
            for yn in (y[0], y[1]):
                # outward div of (xn << PREC) / yn
                numr = xn << PREC
                if yn > 0:
                    lo = shr_down(numr, 0)  # placeholder
                    # floor(numr/yn), ceil(numr/yn)
                    q_lo = shr_down_div(numr, yn)
                    q_hi = shr_up_div(numr, yn)
                else:
                    q_lo = shr_down_div(numr, yn)
                    q_hi = shr_up_div(numr, yn)
                cands_lo.append(q_lo)
                cands_hi.append(q_hi)
        return (min(cands_lo), max(cands_hi))
    return (idiv(numer[0], nrm), idiv(numer[1], nrm))


def shr_down_div(num, den):
    """floor(num/den) for den != 0."""
    if den < 0:
        return -shr_up_div(-num, -den) if False else _floor_div(num, den)
    return _floor_div(num, den)


def _floor_div(n, d):
    # floor(n/d), d can be negative
    q = n // d
    r = n - q * d  # python floor-div already floors for mpz? gmpy2 // floors
    return q


def shr_up_div(num, den):
    q = _floor_div(num, den)
    if num == q * den:
        return q
    return q + 1


def certify_center(cid, center):
    # Newton is a convergence check at the certificate center. The existence
    # box stays centered on that same point, so a successful certificate cannot
    # silently slide over to a different root.
    refined, steps = newton_refine(center, steps=3)
    move = moved(center, refined)
    attempts = []
    chosen = None
    for exp in (40, 56, 72, 88, 104, 120):
        radius = mpz(1) << (PREC - exp)
        try:
            ok, info = krawczyk(center, radius)
        except ZeroDivisionError:
            attempts.append((exp, "singular"))
            continue
        attempts.append((exp, ok, info["rho"], info["eta"]))
        if ok:
            chosen = (center, radius, exp, info)
            break
    if not chosen:
        return {
            "id": cid,
            "ok": False,
            "stage": "krawczyk",
            "newton_steps": steps,
            "move": move,
            "attempts": [(a[0], a[1]) for a in attempts],
        }
    base, radius, exp, info = chosen
    q = info["q"]
    nz = None
    for t, z in enumerate(q):
        if rect_excludes_zero(z):
            nz = t
            break
    stab = stabilizer_ok(base, radius)
    # two fixed raw-component ratios, labels (0,1)/(1,0) and (0,1)/(2,0) if den ok
    # indices in lex order: (0,1)=0, (1,0)=3, (2,0)=10
    ratios = {}
    for name, den_i, num_i in (("r10", 0, 3), ("r20", 0, 10)):
        if rect_excludes_zero(q[den_i]):
            rat = ratio_interval(q[num_i], q[den_i])
            if rat is not None and rect_excludes_zero(q[den_i]):
                ratios[name] = [
                    int(rat[0][0]), int(rat[0][1]), int(rat[1][0]), int(rat[1][1])
                ]
    return {
        "id": cid,
        "ok": bool(nz is not None and stab and ratios.get("r10")),
        "newton_steps": steps,
        "move": move,
        "radius_exp": exp,
        "rho": info["rho"],
        "eta": info["eta"],
        "q_nonzero": nz,
        "stab": stab,
        "ratios": ratios,
        "scale": PREC,
    }


def parse_center(obj):
    scale = int(obj["c_scale"])
    shift = PREC + scale  # c_scale is negative
    if shift < 0:
        raise SystemExit("center finer than PREC")
    out = []
    for re_s, im_s in obj["c"]:
        re = mpz(re_s) << shift
        im = mpz(im_s) << shift
        out.append((re, im))
    if len(out) != 12:
        raise SystemExit("center is not 12 complex coordinates")
    return out


def init_worker():
    global WORLD
    WORLD = World()


def work_file(task):
    path, expect_ids = task
    expect = set(expect_ids)
    found = []
    out = []
    with open(path) as f:
        for line in f:
            obj = json.loads(line)
            cid = int(obj["id"])
            if cid not in expect:
                continue
            found.append(cid)
            center = parse_center(obj)
            # deliberately ignore obj["A"], radius, free_witnesses, q_witness
            t0 = time.perf_counter()
            rec = certify_center(cid, center)
            rec["seconds"] = round(time.perf_counter() - t0, 4)
            out.append(rec)
    missing = sorted(expect - set(found))
    if missing:
        out.append({
            "id": None,
            "ok": False,
            "stage": "missing-ids",
            "file": os.path.basename(path),
            "missing": missing,
        })
    return os.path.basename(path), out


def load_tasks(limit):
    snap = json.loads((NUMDIR / "e44_d7_second_batch_v1_root_snapshot.json").read_text())
    if snap["certified_representatives"] != 21232:
        raise SystemExit("snapshot does not claim 21232")
    tasks = []
    n = 0
    for ch in snap["chunks"]:
        ids = list(ch["ids"])
        if limit is not None and n >= limit:
            break
        if limit is not None and n + len(ids) > limit:
            ids = ids[: limit - n]
        tasks.append((str(NUMDIR / ch["file"]), ids))
        n += len(ids)
        if limit is not None and n >= limit:
            break
    return tasks, n


def negative_self_test():
    """A shifted center must not receive a tiny-box certificate."""
    tasks, _ = load_tasks(1)
    path, ids = tasks[0]
    with open(path) as f:
        obj = json.loads(f.readline())
    center = parse_center(obj)
    # shift real part of a1 by 2^{-8}
    bump = mpz(1) << (PREC - 8)
    bad = [(center[0][0] + bump, center[0][1])] + center[1:]
    radius = mpz(1) << (PREC - 40)
    try:
        ok, _info = krawczyk(bad, radius)
    except ZeroDivisionError:
        ok = False
    if ok:
        raise SystemExit("SELF-TEST FAIL: perturbed center certified")
    print("self-test: perturbed center rejected", flush=True)


def merge_and_separate(records):
    good = [r for r in records if r.get("ok")]
    bad = [r for r in records if not r.get("ok")]
    ids = [r["id"] for r in good]
    # separation by r10 = q_(1,0) / q_(0,1), real part, then imag, then r20
    def key_intervals(r):
        a = r["ratios"]["r10"]
        b = r["ratios"].get("r20")
        return a, b

    order = sorted(good, key=lambda r: (r["ratios"]["r10"][0] + r["ratios"]["r10"][1]))
    # adjacent strict separation on a lexicographic chain of intervals
    def separates(p, q):
        # compare r10 real, then r10 imag, then r20 real, then r20 imag
        pairs = []
        ar = p["ratios"]["r10"]
        br = q["ratios"]["r10"]
        pairs.append((ar[0:2], br[0:2]))
        pairs.append((ar[2:4], br[2:4]))
        if "r20" in p["ratios"] and "r20" in q["ratios"]:
            cr = p["ratios"]["r20"]
            dr = q["ratios"]["r20"]
            pairs.append((cr[0:2], dr[0:2]))
            pairs.append((cr[2:4], dr[2:4]))
        # an interval pair separates if one is entirely left of the other
        for (alo, ahi), (blo, bhi) in ((x, y) for x, y in pairs):
            if ahi < blo or bhi < alo:
                return True
        return False

    # Full pairwise is unnecessary if a sorted key's adjacent intervals are
    # disjoint and the sort agrees with that key. Use real part of r10 first.
    def re_iv(r):
        a = r["ratios"]["r10"]
        return a[0], a[1]

    order = sorted(good, key=lambda r: (r["ratios"]["r10"][0], r["ratios"]["r10"][1], r["id"]))
    adjacent_fail = []
    for i in range(len(order) - 1):
        a = order[i]["ratios"]["r10"]
        b = order[i + 1]["ratios"]["r10"]
        if not (a[1] < b[0]):
            # real parts overlap; try the rest of the invariant on this pair only
            if not separates(order[i], order[i + 1]):
                adjacent_fail.append((order[i]["id"], order[i + 1]["id"]))
    # Adjacent separation on a total order is not enough when the sort key
    # overlaps. Check every overlapping-real cluster exhaustively.
    # Build clusters where consecutive real intervals overlap, then all pairs.
    cluster_fail = list(adjacent_fail)
    # recompute clusters
    clusters = []
    cur = []
    for r in order:
        if not cur:
            cur = [r]
            continue
        if cur[-1]["ratios"]["r10"][1] >= r["ratios"]["r10"][0]:
            cur.append(r)
        else:
            clusters.append(cur)
            cur = [r]
    if cur:
        clusters.append(cur)
    pair_fail = []
    for cl in clusters:
        if len(cl) == 1:
            continue
        for i in range(len(cl)):
            for j in range(i + 1, len(cl)):
                if not separates(cl[i], cl[j]):
                    pair_fail.append((cl[i]["id"], cl[j]["id"]))
    summary = {
        "n_records": len(records),
        "n_ok": len(good),
        "n_bad": len(bad),
        "bad_ids": [r.get("id") for r in bad][:50],
        "bad_stages": [r.get("stage", "certified-false") for r in bad][:50],
        "unique_ids": len(set(ids)),
        "stab_failures": sum(1 for r in records if r.get("stab") is False),
        "q_failures": sum(1 for r in good if r.get("q_nonzero") is None),
        "real_clusters_gt1": sum(1 for cl in clusters if len(cl) > 1),
        "largest_real_cluster": max((len(cl) for cl in clusters), default=0),
        "unseparated_pairs": pair_fail[:20],
        "n_unseparated_pairs": len(pair_fail),
        "newton_step0_max": max((r["newton_steps"][0] for r in good if r.get("newton_steps")), default=None),
        "newton_step_last_max": max((r["newton_steps"][-1] for r in good if r.get("newton_steps")), default=None),
        "move_max": max((r.get("move", 0) for r in good), default=None),
        "radius_exp_min": min((r["radius_exp"] for r in good), default=None),
        "prec": PREC,
    }
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--workers", type=int, default=24)
    ap.add_argument("--bench", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--merge", type=str, default="")
    args = ap.parse_args()
    OUTDIR.mkdir(parents=True, exist_ok=True)
    if args.merge:
        records = []
        for p in sorted(Path(args.merge).glob("part-*.json")):
            records.extend(json.loads(p.read_text()))
        summary = merge_and_separate(records)
        dest = OUTDIR / "summary.json"
        dest.write_text(json.dumps(summary, indent=2))
        print(json.dumps(summary, indent=2))
        return
    init_worker()
    if args.self_test or args.bench:
        negative_self_test()
    tasks, n = load_tasks(1 if args.bench else args.limit)
    print(f"tasks {len(tasks)} roots {n} prec {PREC}", flush=True)
    t0 = time.perf_counter()
    if args.bench:
        recs = []
        for task in tasks:
            name, out = work_file(task)
            recs.extend(out)
            print(name, out[0].get("ok"), "sec", out[0].get("seconds"), "move", out[0].get("move"),
                  "steps", out[0].get("newton_steps"), "rexp", out[0].get("radius_exp"),
                  "rho<", out[0].get("rho"), "eta", out[0].get("eta"), flush=True)
        print("bench_total", round(time.perf_counter() - t0, 3), flush=True)
        (OUTDIR / "bench.json").write_text(json.dumps(recs, indent=2))
        return
    # parallel
    with Pool(args.workers, initializer=init_worker) as pool:
        done = 0
        parts = []
        for name, out in pool.imap_unordered(work_file, tasks, chunksize=1):
            done += 1
            part = OUTDIR / f"part-{name}.json"
            part.write_text(json.dumps(out))
            parts.append(part)
            oks = sum(1 for r in out if r.get("ok"))
            print(f"[{done}/{len(tasks)}] {name} ok {oks}/{len(out)} elapsed {time.perf_counter()-t0:.1f}", flush=True)
    records = []
    for p in parts:
        records.extend(json.loads(p.read_text()))
    summary = merge_and_separate(records)
    summary["elapsed_sec"] = round(time.perf_counter() - t0, 3)
    summary["workers"] = args.workers
    summary["n_scheduled"] = n
    (OUTDIR / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
