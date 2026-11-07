#!/usr/bin/env python3
"""Independent direct-face audit for d=7.

Does not import or read the proposer's generators. The only inputs are the
ACFW definition and the three weight vectors stated in REPORT.md.

  Z(i,j) = b^T D_{(i,j)} a
         = tau^{ij} * sum_k omega^{jk} a_k b_{k+i}
  tau = -exp(i*pi/d) = omega^{(d+1)/2} wait: for d=7, tau = omega^4,
        since omega^4 = exp(8*pi*i/7) = -exp(i*pi/7) = tau,
        and tau^2 = omega.
  (d+1) q_{i,j} = (d+1) Z(i,j) Z(-i,-j) - Z(0)^2
                = (d+1) * omega^{ij} * (sum_k omega^{jk} a_k b_{k+i})
                  * (sum_l omega^{-jl} a_l b_{l-i}) - (sum_k a_k b_k)^2

Chart a_0 = b_1 = 1. Local variables, in order:
  a1,a2,a3,a4,a5,a6, b0,b2,b3,b4,b5,b6.

A direct face at weight w (val(epsilon)=1) is 12 generic elements of
V = L + P, where L is the Q(omega)-span of the weight-exactly-1 parts of
the q-space (after cancellations inside that span) and P is the weight-0
part of a general bihomogeneous (2,2) form. Both pieces sit at order 1
precisely when the minimum weight of the q-span is 1.
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
import ast
import hashlib
import json
import os
import random
import signal
import subprocess
import time
from collections import Counter
from fractions import Fraction
from pathlib import Path

D = 7
DP1 = D + 1  # 8
NAMES = ["a1", "a2", "a3", "a4", "a5", "a6", "b0", "b2", "b3", "b4", "b5", "b6"]
NVAR = 12
FORBIDDEN_PRIMES = {30241, 31081, 65563, 65633, 65761, 65881}
ZERO6 = (0, 0, 0, 0, 0, 0)

CONES = {
    "l1_16": "1/2,1,1,1,3/4,3/4,1/2,0,3/4,1/4,1,1",
    "l1_72": "1/2,1,1,1,2/3,1/3,1/2,0,1/3,2/3,1,1",
    "l2_128": "3/4,1,1/2,1,1/4,1,1/2,3/4,0,1,1/4,1",
}
CLAIMED = {"l1_16": 16, "l1_72": 72, "l2_128": 128}


def cyc_add(a, b):
    return tuple(a[i] + b[i] for i in range(6))


def cyc_sub(a, b):
    return tuple(a[i] - b[i] for i in range(6))


def cyc_scale(a, s):
    return tuple(a[i] * s for i in range(6))


def cyc_is_zero(a):
    return all(x == 0 for x in a)


def cyc_mul(a, b):
    raw = [0] * 13
    for i in range(6):
        if a[i] == 0:
            continue
        ai = a[i]
        for j in range(6):
            if b[j]:
                raw[i + j] += ai * b[j]
    folded = [0] * 7
    for k, v in enumerate(raw):
        if v:
            folded[k % 7] += v
    out = list(folded[:6])
    s = folded[6]
    if s:
        for i in range(6):
            out[i] -= s
    return tuple(out)


def omega_pow(k):
    k %= 7
    if k == 6:
        return (-1, -1, -1, -1, -1, -1)
    return tuple(1 if i == k else 0 for i in range(6))


def cyc_str(a):
    return ",".join(str(x) for x in a)


def self_test_cyclotomic():
    one = omega_pow(0)
    w = omega_pow(1)
    w6 = omega_pow(6)
    assert cyc_mul(w, w6) == one
    acc = ZERO6
    for k in range(7):
        acc = cyc_add(acc, omega_pow(k))
    assert acc == ZERO6
    # tau = omega^4 for d=7, tau^2 = omega
    tau = omega_pow(4)
    assert cyc_mul(tau, tau) == omega_pow(1)
    # (1+omega+...+omega^5) + omega^6 = 0 already checked; omega^6 != 0
    assert omega_pow(6) != ZERO6


def add_term(poly, a_exp, b_exp, coeff):
    if cyc_is_zero(coeff):
        return
    key = tuple(a_exp[1:7] + [b_exp[0]] + b_exp[2:7])
    prev = poly.get(key)
    poly[key] = coeff if prev is None else cyc_add(prev, coeff)


def mul_bilinear(z1, z2):
    """Product of two (1,1)-forms. Each form is a dict (k, bk) -> cyc."""
    acc = {}
    for (k, bk), c1 in z1.items():
        for (l, bl), c2 in z2.items():
            a_exp = [0] * 7
            b_exp = [0] * 7
            a_exp[k] += 1
            a_exp[l] += 1
            b_exp[bk] += 1
            b_exp[bl] += 1
            add_term(acc, a_exp, b_exp, cyc_mul(c1, c2))
    return acc


def Z_without_tau(i, j):
    acc = {}
    for k in range(D):
        acc[(k, (k + i) % D)] = omega_pow((j * k) % D)
    return acc


def closed_q_scaled(i, j):
    """(d+1) * omega^{ij} * Z_notau(i,j) * Z_notau(-i,-j) - Z0^2."""
    prod = mul_bilinear(Z_without_tau(i, j), Z_without_tau((-i) % D, (-j) % D))
    phase = omega_pow((i * j) % D)
    scaled = {}
    for mon, coef in prod.items():
        scaled[mon] = cyc_scale(cyc_mul(phase, coef), DP1)
    z0 = Z_without_tau(0, 0)
    z0sq = mul_bilinear(z0, z0)
    for mon, coef in z0sq.items():
        prev = scaled.get(mon, ZERO6)
        scaled[mon] = cyc_sub(prev, coef)
        if cyc_is_zero(scaled[mon]):
            del scaled[mon]
    return {m: c for m, c in scaled.items() if not cyc_is_zero(c)}


def build_all_q():
    """All 49 polynomials (d+1) q_{i,j}, in lex order of (i,j).

    q_00 = d Z(0)^2 is outside the span of the others (rank 16 versus 15).
    It is not a SIC equation: Y is q_p=0 for p≠0 and Z(0)≠0. Callers that
    build the face of Mq must drop index 0.
    """
    return [closed_q_scaled(i, j) for i in range(D) for j in range(D)]


def sic_generators(polys):
    return polys[1:]


def self_test_product_matches_multiplication():
    """Closed form equals (d+1)*phase*Z*Zminus - Z0^2 by direct multiplication."""
    for i in range(D):
        for j in range(D):
            direct_prod = mul_bilinear(
                Z_without_tau(i, j), Z_without_tau((-i) % D, (-j) % D)
            )
            phase = omega_pow((i * j) % D)
            direct = {}
            for mon, coef in direct_prod.items():
                direct[mon] = cyc_scale(cyc_mul(phase, coef), DP1)
            z0sq = mul_bilinear(Z_without_tau(0, 0), Z_without_tau(0, 0))
            for mon, coef in z0sq.items():
                prev = direct.get(mon, ZERO6)
                direct[mon] = cyc_sub(prev, coef)
            direct = {m: c for m, c in direct.items() if not cyc_is_zero(c)}
            closed = closed_q_scaled(i, j)
            if direct != closed:
                raise SystemExit(f"product mismatch at {(i, j)}")


def parse_weight(s):
    return [Fraction(x) for x in s.split(",")]


def monomial_weight(mon, w):
    return sum(mon[i] * w[i] for i in range(NVAR))


def support_stats(polys, w):
    weights = Counter()
    monomials_by_weight = {}
    n_terms = 0
    for poly in polys:
        for mon, coef in poly.items():
            if cyc_is_zero(coef):
                continue
            n_terms += 1
            wt = monomial_weight(mon, w)
            weights[wt] += 1
            monomials_by_weight.setdefault(wt, set()).add(mon)
    return weights, monomials_by_weight, n_terms


def union_support(polys):
    mons = set()
    for poly in polys:
        for mon, coef in poly.items():
            if not cyc_is_zero(coef):
                mons.add(mon)
    return mons


def degree2_exponents():
    for i in range(D):
        for j in range(i, D):
            exp = [0] * D
            exp[i] += 1
            exp[j] += 1
            yield exp


def perturbation_monomials(w):
    """Weight-0 bihomogeneous (2,2) monomials in the chart a0=b1=1.

    a0 and b1 are the gauge coordinates and have weight 0. Free coordinates
    use `w`.
    """
    found = {}
    for a_exp in degree2_exponents():
        # weight from free a's only; a0 has weight 0
        aw = sum(a_exp[k + 1] * w[k] for k in range(6))
        for b_exp in degree2_exponents():
            # b index: 0->w[6], 1 weight 0, 2->w[7], ..., 6->w[11]
            bw = b_exp[0] * w[6]
            for t in range(5):
                bw += b_exp[t + 2] * w[7 + t]
            if aw + bw != 0:
                continue
            key = tuple(a_exp[1:7] + [b_exp[0]] + b_exp[2:7])
            found[key] = 1
    return sorted(found)


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            return False
        f += 2
    return True


def find_primes(count, start=100000):
    out = []
    n = start
    while len(out) < count:
        if n % 7 == 1 and n not in FORBIDDEN_PRIMES and is_prime(n):
            out.append(n)
        n += 1
    return out


def primitive_7th_root(p):
    assert (p - 1) % 7 == 0
    exp = (p - 1) // 7
    for a in range(2, 200):
        r = pow(a, exp, p)
        if r != 1:
            return r
    raise RuntimeError(f"no 7th root mod {p}")


def eval_cyc(coef, root, p):
    acc = 0
    pw = 1
    for c in coef:
        if c:
            acc = (acc + (c % p) * pw) % p
        pw = pw * root % p
    return acc


def poly_mod_p(poly, root, p, monomials=None):
    out = {}
    items = poly.items() if monomials is None else ((m, poly.get(m, ZERO6)) for m in monomials)
    for mon, coef in items:
        if cyc_is_zero(coef):
            continue
        c = eval_cyc(coef, root, p)
        if c:
            out[mon] = c
    return out


def rref_basis(polys, columns, p):
    """Row-reduce sparse polynomials over F_p. Return a basis (pivot = 1)."""
    rows = [dict(poly) for poly in polys if poly]
    basis = []
    pivot_cols = []
    for col in columns:
        piv = None
        for r in rows:
            if r.get(col, 0) % p != 0:
                piv = r
                break
        if piv is None:
            continue
        inv = pow(piv[col] % p, p - 2, p)
        piv = {m: (c * inv) % p for m, c in piv.items() if (c * inv) % p}
        new_rows = []
        for r in rows:
            if r is piv:
                continue
            coef = r.get(col, 0) % p
            if coef == 0:
                new_rows.append(r)
                continue
            acc = dict(r)
            for m, c in piv.items():
                v = (acc.get(m, 0) - coef * c) % p
                if v:
                    acc[m] = v
                elif m in acc:
                    del acc[m]
            if acc:
                new_rows.append(acc)
        rows = new_rows
        basis.append(piv)
        pivot_cols.append(col)
    return basis, pivot_cols


def combine(basis, coeffs, p):
    acc = {}
    for poly, c in zip(basis, coeffs):
        if c % p == 0:
            continue
        for m, v in poly.items():
            acc[m] = (acc.get(m, 0) + c * v) % p
    return {m: v for m, v in acc.items() if v}


def matrix_rank_rows(rows, p):
    """rows: list of lists over F_p."""
    if not rows:
        return 0
    a = [list(r) for r in rows]
    n = len(a)
    m = len(a[0])
    rank = 0
    col = 0
    while rank < n and col < m:
        piv = None
        for i in range(rank, n):
            if a[i][col] % p:
                piv = i
                break
        if piv is None:
            col += 1
            continue
        a[rank], a[piv] = a[piv], a[rank]
        inv = pow(a[rank][col], p - 2, p)
        for j in range(col, m):
            a[rank][j] = a[rank][j] * inv % p
        for i in range(n):
            if i == rank or a[i][col] % p == 0:
                continue
            factor = a[i][col]
            for j in range(col, m):
                a[i][j] = (a[i][j] - factor * a[rank][j]) % p
        rank += 1
        col += 1
    return rank


def fmt_poly(poly, p):
    parts = []
    for mon in sorted(poly):
        c = poly[mon] % p
        if c == 0:
            continue
        facs = []
        for i, e in enumerate(mon):
            if e == 1:
                facs.append(NAMES[i])
            elif e > 1:
                facs.append(f"{NAMES[i]}^{e}")
        if not facs:
            parts.append(str(c))
        elif c == 1:
            parts.append("*".join(facs))
        else:
            parts.append(str(c) + "*" + "*".join(facs))
    if not parts:
        return "0"
    return "+".join(parts)


def write_msolve(path, polys, p, saturate):
    names = list(NAMES)
    equations = [fmt_poly(poly, p) for poly in polys]
    if saturate:
        names = names + ["zz"]
        prod = "*".join(NAMES)
        equations.append(f"zz*{prod}-1")
    lines = [",".join(names), str(p)]
    for i, eq in enumerate(equations):
        comma = "," if i < len(equations) - 1 else ""
        lines.append(eq + comma)
    path.write_text("\n".join(lines) + "\n")


def rss_kb(pid):
    return resident_bytes(pid) // 1024


def run_msolve(ms_path, out_path, threads, timeout_s, mem_kb, gb=False):
    cmd = [
        executable("msolve"),
        "-f",
        str(ms_path),
        "-o",
        str(out_path),
        "-t",
        str(threads),
        "-v",
        "1",
    ]
    if gb:
        cmd.extend(["-g", "1"])
    log_path = out_path.with_suffix(out_path.suffix + ".log")
    t0 = time.time()
    with log_path.open("w") as log:
        proc = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT)
        killed = None
        while True:
            rc = proc.poll()
            if rc is not None:
                break
            elapsed = time.time() - t0
            mem = rss_kb(proc.pid)
            if mem > mem_kb:
                os.kill(proc.pid, signal.SIGTERM)
                killed = "mem"
                time.sleep(2)
                if proc.poll() is None:
                    os.kill(proc.pid, signal.SIGKILL)
                proc.wait()
                break
            if elapsed > timeout_s:
                os.kill(proc.pid, signal.SIGTERM)
                killed = "time"
                time.sleep(2)
                if proc.poll() is None:
                    os.kill(proc.pid, signal.SIGKILL)
                proc.wait()
                break
            time.sleep(2)
        rc = proc.poll()
    return {
        "returncode": rc,
        "killed": killed,
        "seconds": round(time.time() - t0, 3),
        "rss_kb_at_end": rss_kb(proc.pid) if proc.poll() is None else None,
        "log": str(log_path),
        "out": str(out_path),
    }


def parse_rur(text):
    raw = text.strip()
    if raw.endswith(":"):
        raw = raw[:-1]
    if not raw:
        return {"status": "empty_file"}
    if raw.startswith("[-1]"):
        return {"status": "no_solution", "scheme_length": 0, "minpoly_degree": 0}
    if raw.startswith("[1,"):
        return {"status": "positive_dimension"}
    data = ast.literal_eval(raw)
    if not isinstance(data, list) or not data:
        return {"status": "unparsed", "head": raw[:200]}
    if data[0] == -1:
        return {"status": "no_solution", "scheme_length": 0, "minpoly_degree": 0}
    if data[0] == 1:
        return {"status": "positive_dimension"}
    block = data[1]
    scheme = block[2]
    param = block[5]
    minpoly_deg = param[1][0][0]
    return {
        "status": "finite",
        "scheme_length": scheme,
        "minpoly_degree": minpoly_deg,
        "nvars_reported": block[1],
        "names": block[3],
        "simple": scheme == minpoly_deg,
    }


def parse_monomial(tok):
    tok = tok.strip().rstrip(",")
    if tok in ("", "1"):
        return tuple(0 for _ in range(0))  # sentinel, caller handles
    exp = {}
    for fac in tok.split("*"):
        fac = fac.strip()
        if not fac or fac == "1":
            continue
        if "^" in fac:
            v, e = fac.split("^")
            exp[v] = exp.get(v, 0) + int(e)
        else:
            exp[fac] = exp.get(fac, 0) + 1
    return exp


def parse_leading_ideal(text, names):
    raw = text.strip()
    if raw.endswith(":"):
        raw = raw[:-1]
    # drop header comments
    idx = raw.rfind("[")
    if idx < 0:
        return {"status": "unparsed"}
    body = raw[idx:]
    if body.endswith(":"):
        body = body[:-1]
    try:
        data = ast.literal_eval(body)
    except Exception:
        # msolve prints monomials as bare tokens, not strings: [y^1, x^2]
        inner = body.strip()
        if inner.startswith("["):
            inner = inner[1:]
        if inner.endswith("]"):
            inner = inner[:-1]
        toks = [t.strip() for t in inner.split(",") if t.strip()]
        data = toks
    if data == [1] or data == ["1"]:
        return {"status": "unit_ideal", "length": 0, "zero_dimensional": True}
    gens = []
    name_set = set(names)
    for tok in data:
        if not isinstance(tok, str):
            tok = str(tok)
        exp = parse_monomial(tok)
        if exp == tuple():
            # constant 1
            return {"status": "unit_ideal", "length": 0, "zero_dimensional": True}
        vec = [0] * len(names)
        ok = True
        for v, e in exp.items():
            if v not in name_set:
                ok = False
                break
            vec[names.index(v)] = e
        if not ok:
            return {"status": "bad_monomial", "token": tok}
        gens.append(tuple(vec))
    pure = {}
    for g in gens:
        nz = [(i, e) for i, e in enumerate(g) if e]
        if len(nz) == 1:
            i, e = nz[0]
            pure[i] = min(pure.get(i, e), e)
    zero_dim = all(i in pure for i in range(len(names)))
    if not zero_dim:
        return {
            "status": "not_zero_dimensional",
            "nlead": len(gens),
            "pure_powers": {names[i]: e for i, e in pure.items()},
        }
    # BFS staircase
    from collections import deque

    gens_sorted = gens
    limit = 2_000_000
    seen = {tuple(0 for _ in names)}
    q = deque(seen)
    while q:
        mon = q.popleft()
        for i in range(len(names)):
            if mon[i] + 1 > pure[i]:
                continue
            nxt = list(mon)
            nxt[i] += 1
            nt = tuple(nxt)
            if nt in seen:
                continue
            if any(all(nt[j] >= g[j] for j in range(len(names))) for g in gens_sorted):
                continue
            seen.add(nt)
            if len(seen) > limit:
                return {"status": "staircase_overflow", "nlead": len(gens)}
            q.append(nt)
    return {
        "status": "zero_dimensional",
        "length": len(seen),
        "nlead": len(gens),
        "pure_powers": {names[i]: e for i, e in pure.items()},
    }


def leading_parts(polys, w):
    out = []
    mons = set()
    for poly in polys:
        part = {}
        for mon, coef in poly.items():
            if cyc_is_zero(coef):
                continue
            if monomial_weight(mon, w) == 1:
                part[mon] = coef
                mons.add(mon)
        if part:
            out.append(part)
    return out, sorted(mons)


def full_q_rank_mod_p(polys, root, p):
    mons = sorted(union_support(polys))
    rows = []
    for poly in polys:
        red = poly_mod_p(poly, root, p)
        rows.append([red.get(m, 0) for m in mons])
    # drop zero rows
    rows = [r for r in rows if any(r)]
    return matrix_rank_rows(rows, p), len(mons)


def matrix_check(root, p, n_points=3):
    """Compare every (d+1)q_ij with b^T D a on the chart a0=b1=1."""
    rng = random.Random(p * 17 + 3)
    tau = pow(root, 4, p)  # tau = omega^4
    mismatches = 0
    polys = build_all_q()
    for _ in range(n_points):
        free = [rng.randrange(1, p) for _ in range(NVAR)]
        a = [0] * D
        b = [0] * D
        a[0] = 1
        b[1] = 1
        for i in range(6):
            a[i + 1] = free[i]
        b[0] = free[6]
        for i in range(5):
            b[i + 2] = free[7 + i]

        def apply_D(vec, p1, p2):
            phase = pow(tau, (p1 * p2) % (2 * D), p)
            out = [0] * D
            for k in range(D):
                src = (k - p1) % D
                ow = pow(root, (p2 * src) % D, p)
                out[k] = phase * ow * vec[src] % p
            return out

        def Z(p1, p2):
            dv = apply_D(a, p1, p2)
            return sum(b[k] * dv[k] for k in range(D)) % p

        # Also the sum formula, as a second witness.
        def Z_sum(i, j):
            phase = pow(tau, (i * j) % (2 * D), p)
            acc = 0
            for k in range(D):
                acc = (acc + pow(root, (j * k) % D, p) * a[k] * b[(k + i) % D]) % p
            return phase * acc % p

        for i in range(D):
            for j in range(D):
                if Z(i, j) != Z_sum(i, j):
                    mismatches += 1
        # polynomial vs (d+1) Z Zminus - Z0^2
        z0 = Z(0, 0)
        env = dict(zip(NAMES, free))
        for idx, poly in enumerate(polys):
            i, j = divmod(idx, D)
            red = poly_mod_p(poly, root, p)
            val = 0
            for mon, c in red.items():
                t = c
                for name, e in zip(NAMES, mon):
                    if e:
                        t = t * pow(env[name], e, p) % p
                val = (val + t) % p
            expect = (DP1 * Z(i, j) * Z((-i) % D, (-j) % D) - z0 * z0) % p
            if val != expect:
                mismatches += 1
    return mismatches


def hash_mons(mons):
    h = hashlib.sha256()
    for mon in sorted(mons):
        h.update(",".join(map(str, mon)).encode())
        h.update(b"\n")
    return h.hexdigest()


def analyze_cone(tag, polys, primes):
    w = parse_weight(CONES[tag])
    weights, by_w, n_terms = support_stats(polys, w)
    ordered = sorted(weights)
    min_w = ordered[0]
    exact_support = union_support(polys)
    below = []
    for wt in ordered:
        if wt < 1:
            below.append({"weight": str(wt), "n_monomials": len(by_w[wt])})
    at1 = sorted(by_w.get(1, []))
    lead_polys, lead_mons = leading_parts(polys, w)
    p_mons = perturbation_monomials(w)
    info = {
        "tag": tag,
        "claimed_length": CLAIMED[tag],
        "weight": CONES[tag],
        "exact_support_count": len(exact_support),
        "exact_support_sha256": hash_mons(exact_support),
        "generator_term_occurrences": n_terms,
        "min_weight": str(min_w),
        "min_weight_is_one": min_w == 1,
        "weights_below_one": below,
        "n_monomials_at_weight_one": len(at1),
        "weight_one_sha256": hash_mons(at1),
        "smallest_weights": [
            {"weight": str(wt), "n_monomials": len(by_w[wt])} for wt in ordered[:8]
        ],
        "perturbation_monomials": [list(m) for m in p_mons],
        "dim_P": len(p_mons),
        "primes": {},
    }
    for p in primes:
        root = primitive_7th_root(p)
        q_rank, nmons = full_q_rank_mod_p(polys, root, p)
        lead_mod = [poly_mod_p(poly, root, p) for poly in lead_polys]
        lead_mod = [poly for poly in lead_mod if poly]
        columns = sorted(set().union(*lead_mod)) if lead_mod else []
        basis_L, piv_L = rref_basis(lead_mod, columns, p)
        p_polys = []
        for mon in p_mons:
            p_polys.append({mon: 1})
        # P is weight 0 and disjoint from L; still row-reduce the sum
        # in case a bad prime created an overlap (it should not).
        sum_polys = basis_L + p_polys
        sum_cols = sorted(set().union(*[set(poly) for poly in sum_polys])) if sum_polys else []
        basis_V, piv_V = rref_basis(sum_polys, sum_cols, p)
        # monomials killed by reduction
        exact_at1 = set(at1)
        mod_at1 = set()
        for poly in lead_mod:
            mod_at1.update(poly)
        info["primes"][str(p)] = {
            "primitive_7th_root": root,
            "q_rank": q_rank,
            "q_support_mod_p": nmons,
            "dim_L": len(basis_L),
            "dim_V": len(basis_V),
            "n_weight1_monomials_surviving": len(mod_at1),
            "weight1_monomials_killed": len(exact_at1 - mod_at1),
            "dim_P": len(p_mons),
        }
        info["primes"][str(p)]["_basis_V"] = basis_V
    return info


def random_full_rank_matrix(rng, rows, cols, p):
    while True:
        mat = [[rng.randrange(0, p) for _ in range(cols)] for _ in range(rows)]
        if matrix_rank_rows(mat, p) == min(rows, cols):
            return mat


def strip_private(info):
    import copy

    out = copy.deepcopy(info)
    for pdata in out["primes"].values():
        pdata.pop("_basis_V", None)
    return out


def solve_cone(info, work, threads, timeout_s, mem_kb, seeds, do_naive, with_gb):
    results = []
    tag = info["tag"]
    for p_str, pdata in info["primes"].items():
        p = int(p_str)
        basis = pdata["_basis_V"]
        dim_v = len(basis)
        for seed in seeds:
            rng = random.Random(seed)
            label = f"{tag}_p{p}_s{seed}"
            if dim_v < NVAR:
                equations_src = basis
                mode = "underdetermined_span"
            elif dim_v == NVAR:
                equations_src = basis
                mode = "square_full_span"
            else:
                mat = random_full_rank_matrix(rng, NVAR, dim_v, p)
                equations_src = [combine(basis, row, p) for row in mat]
                mode = "generic_12_plane"
            for saturate in (True,):
                ms = work / f"{label}_sat{int(saturate)}.ms"
                rur = work / f"{label}_sat{int(saturate)}.rur"
                gb = work / f"{label}_sat{int(saturate)}.gb"
                write_msolve(ms, equations_src, p, saturate=saturate)
                print(f"RUN {label} mode={mode} dimV={dim_v}", flush=True)
                rur_run = run_msolve(ms, rur, threads, timeout_s, mem_kb, gb=False)
                if with_gb:
                    gb_run = run_msolve(ms, gb, threads, timeout_s, mem_kb, gb=True)
                    gb_text = gb.read_text() if gb.exists() else ""
                else:
                    gb_run = {"returncode": None, "killed": "skipped", "seconds": 0, "log": "", "out": ""}
                    gb_text = ""
                rur_text = rur.read_text() if rur.exists() else ""
                parsed = parse_rur(rur_text) if rur_run["killed"] is None and rur_run["returncode"] == 0 else {
                    "status": "solver_failed"
                }
                names = NAMES + ["zz"]
                if gb_run.get("killed") == "skipped":
                    stair = {"status": "skipped"}
                elif gb_run["killed"] is None and gb_run["returncode"] == 0:
                    stair = parse_leading_ideal(gb_text, names)
                else:
                    stair = {"status": "solver_failed"}
                rec = {
                    "label": label,
                    "p": p,
                    "seed": seed,
                    "mode": mode,
                    "dim_V": dim_v,
                    "claimed": CLAIMED[tag],
                    "rur": parsed,
                    "staircase": {k: v for k, v in stair.items() if k != "pure_powers"}
                    | ({"pure_powers": stair.get("pure_powers")} if "pure_powers" in stair else {}),
                    "rur_run": {k: v for k, v in rur_run.items() if k != "rss_kb_at_end"},
                    "gb_run": {k: v for k, v in gb_run.items() if k != "rss_kb_at_end"},
                }
                # agreement
                if parsed.get("status") == "finite" and stair.get("status") == "zero_dimensional":
                    rec["length_agree"] = parsed["scheme_length"] == stair["length"]
                results.append(rec)
                print(
                    f"DONE {label} rur={parsed.get('status')} "
                    f"len={parsed.get('scheme_length')} minpoly={parsed.get('minpoly_degree')} "
                    f"stair={stair.get('status')} slen={stair.get('length')} "
                    f"sec={rur_run['seconds']}",
                    flush=True,
                )
        if do_naive:
            # Independent coefficients on the full monomial support of V.
            support = sorted(set().union(*[set(poly) for poly in basis])) if basis else []
            rng = random.Random(seeds[0] + 99)
            naive = []
            for _ in range(NVAR):
                poly = {}
                for mon in support:
                    c = rng.randrange(0, p)
                    if c:
                        poly[mon] = c
                naive.append(poly)
            label = f"{tag}_p{p}_naive"
            ms = work / f"{label}.ms"
            rur = work / f"{label}.rur"
            write_msolve(ms, naive, p, saturate=True)
            print(f"RUN {label} support={len(support)}", flush=True)
            rur_run = run_msolve(ms, rur, threads, timeout_s, mem_kb, gb=False)
            rur_text = rur.read_text() if rur.exists() else ""
            parsed = parse_rur(rur_text) if rur_run["returncode"] == 0 and rur_run["killed"] is None else {
                "status": "solver_failed"
            }
            results.append(
                {
                    "label": label,
                    "p": p,
                    "mode": "naive_full_support",
                    "support": len(support),
                    "rur": parsed,
                    "rur_run": {k: v for k, v in rur_run.items() if k != "rss_kb_at_end"},
                }
            )
            print(
                f"DONE {label} rur={parsed.get('status')} len={parsed.get('scheme_length')} "
                f"minpoly={parsed.get('minpoly_degree')}",
                flush=True,
            )
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--work", default=str(public_root(__file__) / "work/faces/work"))
    ap.add_argument("--out", default=str(public_root(__file__) / "work/faces/out"))
    ap.add_argument("--only", default="l1_72,l1_16,l2_128")
    ap.add_argument("--primes", type=int, default=2)
    ap.add_argument("--prime-start", type=int, default=100000)
    ap.add_argument("--seeds", default="8675309,42424249")
    ap.add_argument("--threads", type=int, default=8)
    ap.add_argument("--timeout", type=int, default=2400)
    ap.add_argument("--mem-gb", type=int, default=100)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument("--naive", action="store_true")
    ap.add_argument("--skip-build-check", action="store_true")
    ap.add_argument("--with-gb", action="store_true")
    args = ap.parse_args()
    work = Path(args.work)
    out = Path(args.out)
    work.mkdir(parents=True, exist_ok=True)
    out.mkdir(parents=True, exist_ok=True)

    print("self-test cyclotomic", flush=True)
    self_test_cyclotomic()
    if not args.skip_build_check:
        print("self-test product expansion", flush=True)
        self_test_product_matches_multiplication()
    print("build q", flush=True)
    t0 = time.time()
    polys_all = build_all_q()
    polys = sic_generators(polys_all)
    support = union_support(polys)
    print(
        f"sic generators={len(polys)} (q_00 dropped) union_support={len(support)} "
        f"build_seconds={time.time()-t0:.3f}",
        flush=True,
    )
    primes = find_primes(args.primes, args.prime_start)
    print("primes", primes, flush=True)
    root0 = primitive_7th_root(primes[0])
    mismatches = matrix_check(root0, primes[0])
    rank_all, nmon_all = full_q_rank_mod_p(polys_all, root0, primes[0])
    rank0, nmon0 = full_q_rank_mod_p(polys, root0, primes[0])
    print(
        f"matrix_mismatches={mismatches} rank_with_q00={rank_all} "
        f"rank_sic={rank0} on {nmon0} monomials",
        flush=True,
    )

    tags = [t.strip() for t in args.only.split(",") if t.strip()]
    seeds = [int(s) for s in args.seeds.split(",") if s]
    summary = {
        "primes": primes,
        "forbidden_primes_avoided": sorted(FORBIDDEN_PRIMES),
        "q_union_support_excluding_q00": len(support),
        "matrix_vs_definition_mismatches": mismatches,
        "q_rank_with_q00": rank_all,
        "q_rank_sic": {"p": primes[0], "rank": rank0, "monomials": nmon0},
        "cones": {},
        "solves": {},
    }
    mem_kb = args.mem_gb * 1024 * 1024
    for tag in tags:
        print(f"ANALYZE {tag}", flush=True)
        info = analyze_cone(tag, polys, primes)
        public = strip_private(info)
        summary["cones"][tag] = public
        (out / f"{tag}_analysis.json").write_text(json.dumps(public, indent=2))
        print(json.dumps(public, indent=2), flush=True)
        if args.solve:
            solved = solve_cone(
                info,
                work,
                args.threads,
                args.timeout,
                mem_kb,
                seeds,
                args.naive,
                args.with_gb,
            )
            summary["solves"][tag] = solved
            (out / f"{tag}_solve.json").write_text(json.dumps(solved, indent=2))
    (out / "summary.json").write_text(json.dumps(summary, indent=2))
    print("WROTE", out / "summary.json", flush=True)


if __name__ == "__main__":
    main()
