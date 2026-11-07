#!/usr/bin/env python3.14
"""Exact direct initial systems for M*q + epsilon*R, seed 20261102.

This implements the GLOBAL minimum convention of the original trop.jl.  It
does not replace that system by the entire filtered initial vector space.
Polynomials are dictionaries exponent_tuple -> coefficient.  Exact coefficients
are integer vectors modulo Phi_d, after multiplying every q by d+1.  Modular
coefficients are integers modulo p.  No floating-point arithmetic is used.
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
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
SEED = 20261102
Exp = tuple[int, ...]
Poly = dict[Exp, object]


def factor_primes(n):
    out = set()
    k = 2
    while k * k <= n:
        while n % k == 0:
            out.add(k)
            n //= k
        k += 1
    if n > 1:
        out.add(n)
    return out


def primitive_root(p):
    ff = factor_primes(p - 1)
    return next(g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in ff))


@lru_cache(None)
def root_vectors(d):
    """Vectors of 1,zeta,...,zeta^(d-1) in Z[zeta]/Phi_d."""
    import sympy as sp
    z = sp.Symbol("z")
    cc = [int(x) for x in reversed(sp.Poly(sp.cyclotomic_poly(d, z), z).all_coeffs())]
    deg = len(cc) - 1
    out = []
    for k in range(d):
        vv = [0] * max(d, deg + 1)
        vv[k] = 1
        for j in range(len(vv) - 1, deg - 1, -1):
            if vv[j]:
                value = vv[j]
                for i in range(deg + 1):
                    vv[j - deg + i] -= value * cc[i]
        out.append(tuple(vv[:deg]))
    return tuple(out), tuple(cc)


@dataclass
class Chart:
    d: int
    c: int
    s: int
    p: int | None
    names: tuple[str, ...]
    keep: tuple[int, ...]
    labels: tuple[tuple[int, int], ...]
    q: tuple[Poly, ...]
    r_support: tuple[Exp, ...]
    omega: int | None
    cyclotomic: tuple[int, ...]

    @property
    def n(self):
        return 2 * self.d - 2

    @property
    def support(self):
        return tuple(sorted(set().union(*(f.keys() for f in self.q))))


@lru_cache(None)
def build_chart(d: int, c: int = 0, s: int = 1, p: int | None = None) -> Chart:
    """Build exact dehomogenized q and complete (2,2) perturbation support.

    Variable order: a_k (increasing, k!=c), then b_k (increasing, k!=s).
    a_c=b_s=1.  q entries are (d+1)*Z(p)Z(-p)-Z(0)^2.
    Taking the product first avoids the even-d representative-phase error:
    coefficient of a_k*a_l*b_(k+i)*b_(l-i) is zeta^(j*(i+k-l)).
    """
    if not (d >= 2 and 0 <= c < d and 0 <= s < d):
        raise ValueError("invalid chart")
    roots, cyclo = root_vectors(d)
    if p is not None:
        if (p - 1) % (2 * d):
            raise ValueError("p must satisfy 2*d | p-1")
        if p == d + 1:
            raise ValueError("bad characteristic divides d+1")
        omega = pow(primitive_root(p), (p - 1) // d, p)
        root = [pow(omega, k, p) for k in range(d)]
        zero = 0
        def add_coeff(a, b): return (a + b) % p
        def scaled_root(k, m): return root[k % d] * m % p
    else:
        omega = None
        zero = (0,) * (len(cyclo) - 1)
        def add_coeff(a, b): return tuple(x + y for x, y in zip(a, b))
        def scaled_root(k, m): return tuple(m * x for x in roots[k % d])
    keep = tuple([k for k in range(d) if k != c] + [d+k for k in range(d) if k != s])
    names = tuple([f"a{k}" for k in range(d) if k != c] + [f"b{k}" for k in range(d) if k != s])
    def exp_of(indices):
        ee = [0] * (2*d)
        for k in indices: ee[k] += 1
        return tuple(ee[k] for k in keep)
    seen = set()
    labels, q = [], []
    for i in range(d):
        for j in range(d):
            if (i, j) == (0, 0) or (i, j) in seen: continue
            seen.update(((i, j), ((-i) % d, (-j) % d)))
            poly = {}
            for k in range(d):
                for l in range(d):
                    e = exp_of((k, l, d+(k+i) % d, d+(l-i) % d))
                    poly[e] = add_coeff(poly.get(e, zero), scaled_root(j*(i+k-l), d+1))
                    e0 = exp_of((k, l, d+k, d+l))
                    poly[e0] = add_coeff(poly.get(e0, zero), scaled_root(0, -1))
            q.append({e: cc for e, cc in poly.items() if cc != zero})
            labels.append((i, j))
    support = set()
    for aa in itertools.combinations_with_replacement(range(d), 2):
        for bb in itertools.combinations_with_replacement(range(d), 2):
            support.add(exp_of((*aa, *(d+k for k in bb))))
    return Chart(d, c, s, p, names, keep, tuple(labels), tuple(q), tuple(sorted(support)), omega, cyclo)


@dataclass
class Face:
    chart: Chart
    w: tuple[Fraction, ...]
    order: Fraction
    forms: tuple[Poly, ...]
    r_monomials: tuple[Exp, ...]

    @property
    def support(self):
        return tuple(sorted(set(self.r_monomials).union(*(f.keys() for f in self.forms))))


def face_at(chart: Chart, w, eps_weight=1) -> Face:
    """GLOBAL lowest forms, with exact rational weights and cancellations."""
    w = tuple(Fraction(x) for x in w)
    if len(w) != chart.n: raise ValueError("wrong weight length")
    dot = lambda e: sum(x*y for x, y in zip(e, w))
    orders = [min(map(dot, f)) for f in chart.q]
    order_r = Fraction(eps_weight) + min(map(dot, chart.r_support))
    m = min(min(orders), order_r)
    forms = tuple({e: cc for e, cc in f.items() if dot(e) == m}
                  for f, order in zip(chart.q, orders) if order == m)
    rr = tuple(e for e in chart.r_support if Fraction(eps_weight) + dot(e) == m)
    return Face(chart, w, m, forms, rr)


def row_reduce(polys, p):
    """Canonical F_p row space of polynomial coefficient vectors."""
    if not polys: return []
    mons = sorted(set().union(*(f.keys() for f in polys)), reverse=True)
    rows = [[int(f.get(e, 0)) % p for e in mons] for f in polys]
    rr = 0
    for j in range(len(mons)):
        pivot = next((i for i in range(rr, len(rows)) if rows[i][j]), None)
        if pivot is None: continue
        rows[rr], rows[pivot] = rows[pivot], rows[rr]
        inv = pow(rows[rr][j], -1, p)
        rows[rr] = [x*inv % p for x in rows[rr]]
        for i in range(len(rows)):
            if i != rr and rows[i][j]:
                factor = rows[i][j]
                rows[i] = [(x - factor*y) % p for x, y in zip(rows[i], rows[rr])]
        rr += 1
        if rr == len(rows): break
    return [{e: x for e, x in zip(mons, row) if x} for row in rows[:rr]]


def generic_square(face: Face, seed=SEED, coefficient_bound=1000000, reduce_rows=True):
    """n independent generic elements, deterministic integer coefficients.

    The exact same coefficient choices are used across primes because the
    original generator/monomial order is fixed before reduction.  Row reduction
    changes only the displayed generating set over the selected finite field.
    """
    p = face.chart.p
    if p is None: raise ValueError("generic_square currently needs modular chart")
    rand = random.Random(seed)
    rows = []
    for _ in range(face.chart.n):
        poly = {}
        for f in face.forms:
            cc = rand.randint(-coefficient_bound, coefficient_bound)
            for e, x in f.items(): poly[e] = (poly.get(e, 0) + cc*x) % p
        for e in face.r_monomials:
            cc = rand.randint(-coefficient_bound, coefficient_bound)
            poly[e] = (poly.get(e, 0) + cc) % p
        rows.append({e: cc for e, cc in poly.items() if cc})
    return row_reduce(rows, p) if reduce_rows else rows


def poly_string(poly, names):
    if not poly: return "0"
    return "+".join(str(cc) + "".join(f"*{names[j]}^{k}" for j, k in enumerate(e) if k)
                    for e, cc in sorted(poly.items(), reverse=True))


def singular_program(polys, p, names, reducedness=True, strategy="sat", algorithm="std"):
    """Saturated F_p length and Jacobian test, with no iteration cutoff.

    For square n-generator systems, J + det(dF/dx)=(1) certifies the torus
    quotient is finite etale and every geometric point has multiplicity one.
    If fewer than n generators remain after row reduction this criterion is
    not run; a nonempty ideal cannot then be a zero-dimensional complete
    intersection in the ambient n-torus.
    """
    n = len(names)
    ff = ",".join(poly_string(f, names) for f in polys) or "0"
    if algorithm not in ("std", "slimgb"): raise ValueError("unknown algorithm")
    if strategy not in ("sat", "colon", "rabinowitsch"): raise ValueError("unknown saturation")
    src = [f'LIB "elim.lib";\nring r={p},({",".join(names)}),dp;',
           'option(redSB);', f'ideal I={ff};', f'poly h={"*".join(names)};',
           'print("STAGE groebner");', f'ideal G={algorithm}(I);',
           'print("STAGE saturate");']
    if strategy == "sat":
        src += ['ideal J=sat(G,ideal(h));']
    elif strategy == "colon":
        src += ['ideal J=G; ideal K; int steps=0;',
                'while(1){ K=std(quotient(J,ideal(h))); steps++; if(size(reduce(K,J))==0){break;} J=K; }',
                'J=K; print("SAT_STEPS "+string(steps));']
    else:
        src += [f'ring invr={p},(tt,{",".join(names)}),(dp(1),dp({n}));',
                'ideal II=imap(r,I),1-tt*imap(r,h);', f'ideal JJ={algorithm}(II);',
                'ideal EE=eliminate(JJ,tt); setring r; ideal J=std(imap(invr,EE));']
    src += ['int dd=dim(J); int ll=vdim(J);',
            'print("COUNT dim="+string(dd)+" length="+string(ll));']
    if reducedness and len(polys) == n:
        src += ['if(dd==0){', 'print("STAGE jacobian");',
                'matrix JJ=jacob(I);', 'qring qr=J;',
                'matrix JQ=imap(r,JJ); poly detJ=det(JQ);',
                'ideal bad=std(ideal(detJ));',
                'print("REDUCED "+string(reduce(1,bad)==0));', 'setring r;',
                '} else {if(dd<0){print("REDUCED 1");} else {print("REDUCED -1");}}']
    else:
        src += ['print("REDUCED -1");']
    src += ['quit;']
    return "\n".join(src) + "\n"


def singular_torus_count(polys, p, names, *, timeout=600, reducedness=True,
                         strategy="sat", algorithm="std", memory_gb=9,
                         singular=None):
    """One Singular process, deterministic input; returns FAIL rather than 0 on errors."""
    singular=singular or shutil.which("Singular") or "Singular"
    source = singular_program(polys, p, names, reducedness, strategy, algorithm)
    sha = hashlib.sha256(source.encode()).hexdigest()
    env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")
    def limits():
        # macOS RLIMIT_AS is unsupported for some builds.  The coordinator also
        # monitors RSS; this applies a best-effort address-space cap where valid.
        if sys.platform != "darwin":
            resource.setrlimit(resource.RLIMIT_AS, (memory_gb*1024**3, memory_gb*1024**3))
    started = time.monotonic()
    temp_root=os.environ.get("NF6_DATA_DIR")
    if temp_root: Path(temp_root).mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="nf6-face-",dir=temp_root) as tmp:
        path = Path(tmp)/"face.sing"
        path.write_text(source)
        proc = subprocess.Popen([singular, "--no-rc", "-q", str(path)], stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, env=env, preexec_fn=limits)
        try:
            out, _ = proc.communicate(timeout=timeout)
            timed_out = False
        except subprocess.TimeoutExpired:
            proc.terminate()  # only the exact process created above
            try: out, _ = proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                out, _ = proc.communicate()
            timed_out = True
    count = re.search(r"COUNT dim=(-?\d+) length=(-?\d+)", out)
    reduced = re.search(r"REDUCED (-?\d+)", out)
    errors = [line for line in out.splitlines() if "?" in line or "error" in line.lower()]
    ok = not timed_out and proc.returncode == 0 and count is not None and not errors
    return dict(status="PASS" if ok else "TIMEOUT" if timed_out else "ERROR", p=p,
                dim=int(count[1]) if count else None,
                length=max(0, int(count[2])) if count and int(count[1]) < 0 else int(count[2]) if count else None,
                reduced=(reduced[1] == "1") if reduced and reduced[1] != "-1" else None,
                seconds=round(time.monotonic()-started, 6), pid=proc.pid,
                source_sha256=sha, stdout=out, errors=errors,
                saturation=strategy, algorithm=algorithm, seed=SEED)


def count_face(d, c, s, w, p, seed=SEED, **kwargs):
    chart = build_chart(d, c, s, p)
    exact = face_at(build_chart(d, c, s), w)
    face = face_at(chart, w)
    # A finite-field cancellation changing the face would invalidate comparison.
    if [set(f) for f in face.forms] != [set(f) for f in exact.forms]:
        raise ValueError("bad prime: face support changed")
    rows = generic_square(face, seed)
    ans = singular_torus_count(rows, p, chart.names, **kwargs)
    ans.update(d=d, chart=[c,s], w=list(map(str, face.w)), order=str(face.order),
               q_forms=len(face.forms), r_monomials=len(face.r_monomials),
               face_rank=len(row_reduce(list(face.forms)+[{e:1} for e in face.r_monomials], p)),
               square_rank=len(rows))
    return ans


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("d", type=int)
    ap.add_argument("c", type=int)
    ap.add_argument("s", type=int)
    ap.add_argument("w", help="comma-separated exact rational weights")
    ap.add_argument("--p", type=int, default=30241)
    ap.add_argument("--timeout", type=float, default=600)
    ap.add_argument("--seed", type=int, default=SEED)
    ap.add_argument("--strategy", choices=["sat","colon","rabinowitsch"], default="sat")
    ap.add_argument("--algorithm", choices=["std","slimgb"], default="std")
    ap.add_argument("--no-reducedness", action="store_true")
    ap.add_argument("--emit-singular", action="store_true")
    args = ap.parse_args()
    ww = tuple(map(Fraction,args.w.split(",")))
    if args.emit_singular:
        ff = face_at(build_chart(args.d,args.c,args.s,args.p),ww)
        print(singular_program(generic_square(ff,args.seed),args.p,ff.chart.names,
                               not args.no_reducedness,args.strategy,args.algorithm),end="")
    else:
        print(json.dumps(count_face(args.d,args.c,args.s,ww,args.p,args.seed,
             timeout=args.timeout,reducedness=not args.no_reducedness,
             strategy=args.strategy,algorithm=args.algorithm),sort_keys=True),flush=True)


if __name__ == "__main__": main()
