#!/usr/bin/env python3.14
"""Exact denominator-free enumeration of nondegenerate direct-face candidates.

The covered family is the GLOBAL-minimum face of generic M*q+epsilon*R,
not the higher filtered initial vector space. See ../ENUMERATION.md.
All support cancellation, ranks, feasibility, and coverage checks are exact.
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
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
import z3
from e10_face_system import SEED, build_chart


def rref(rows):
    """Exact row basis, pivots, and original independent-row indices."""
    if not rows:
        return [], [], []
    mat = [[Fraction(x) for x in row] for row in rows]
    tags = list(range(len(mat)))
    pivots, independent = [], []
    k = 0
    for j in range(len(mat[0])):
        pp = next((i for i in range(k, len(mat)) if mat[i][j]), None)
        if pp is None:
            continue
        mat[k], mat[pp] = mat[pp], mat[k]
        tags[k], tags[pp] = tags[pp], tags[k]
        scale = mat[k][j]
        mat[k] = [x/scale for x in mat[k]]
        for i in range(len(mat)):
            if i != k and mat[i][j]:
                scale = mat[i][j]
                mat[i] = [x-scale*y for x, y in zip(mat[i], mat[k])]
        pivots.append(j)
        independent.append(tags[k])
        k += 1
        if k == len(mat):
            break
    return mat[:k], pivots, independent


def in_span(row, basis, pivots):
    vv = [Fraction(x) for x in row]
    for bb, j in zip(basis, pivots):
        scale = vv[j]
        if scale:
            vv = [x-scale*y for x, y in zip(vv, bb)]
    return not any(vv)


def determinant(rows):
    mat = [[Fraction(x) for x in row] for row in rows]
    out = Fraction(1)
    for j in range(len(mat)):
        pp = next((i for i in range(j, len(mat)) if mat[i][j]), None)
        if pp is None:
            return Fraction(0)
        if pp != j:
            mat[j], mat[pp] = mat[pp], mat[j]
            out = -out
        scale = mat[j][j]
        out *= scale
        for i in range(j+1, len(mat)):
            factor = mat[i][j]/scale
            if factor:
                mat[i] = [x-factor*y for x, y in zip(mat[i], mat[j])]
    return out


def minimal_exponents(exponents):
    """Discard exact redundancies for weights strictly positive in every slot."""
    out = []
    for ee in sorted(set(exponents), key=lambda e: (sum(e), e)):
        if not any(all(x <= y for x, y in zip(ff, ee)) for ff in out):
            out.append(ee)
    return tuple(out)


def exact_value(value):
    return Fraction(value.numerator_as_long(), value.denominator_as_long())


def enumerate_vertices(d, c=0, s=1, zero_names=(), timeout=0, limit=0, progress=True):
    start = time.monotonic()
    chart = build_chart(d, c, s)
    zero_names = tuple(sorted(zero_names, key=chart.names.index))
    if len(set(zero_names)) != len(zero_names):
        raise ValueError("duplicate zero variable")
    zi = tuple(chart.names.index(nm) for nm in zero_names)
    free = tuple(j for j in range(chart.n) if j not in zi)
    exps = minimal_exponents(tuple(tuple(e[j] for j in free) for e in chart.support))
    kk = len(free)
    solver = z3.Solver()
    solver.set(random_seed=SEED)
    if timeout:
        solver.set(timeout=timeout*1000)
    ww = tuple(z3.Real(chart.names[j]) for j in free)
    lin = [z3.Sum([a*x for a, x in zip(e, ww) if a]) for e in exps]
    eqs = [term == 1 for term in lin]
    solver.add(*(w > 0 for w in ww))
    solver.add(*(term >= 1 for term in lin))
    # Full rank requires at least k active inequalities. Exact pseudo-Boolean
    # count is only a necessary filter. The independent-rank check is below.
    solver.add(z3.PbGe([(eq, 1) for eq in eqs], kk))
    digest = hashlib.sha256(json.dumps([chart.names, chart.support], separators=(",", ":")).encode()).hexdigest()
    out = dict(format="sic-direct-face-vertices-v1", d=d, c=c, s=s,
               names=list(chart.names), zero_names=list(zero_names),
               positive_names=[chart.names[j] for j in free],
               seed=SEED, python=sys.version, z3=z3.get_version_string(),
               support_sha256=digest, char0_support_count=len(chart.support),
               minimal_projected_support_count=len(exps),
               projected_exponents=[list(e) for e in exps],
               weights=[], rank_cuts=0, solver_models=0, complete=False,
               coverage="all strict-positive vertices of exact blocking polyhedron for specified zero coordinates; hence all nonsingular isolated global-minimum faces in that stratum")
    seen = set()
    last = start
    while True:
        result = solver.check()
        if result == z3.unsat:
            out.update(complete=True, termination="unsat")
            break
        if result != z3.sat:
            out.update(termination="unknown", reason=solver.reason_unknown())
            break
        model = solver.model()
        value = tuple(exact_value(model.eval(x, model_completion=True)) for x in ww)
        active = [i for i, ee in enumerate(exps) if sum(x*y for x, y in zip(ee, value)) == 1]
        basis, pivots, tags = rref([exps[i] for i in active])
        out["solver_models"] += 1
        if len(pivots) < kk:
            # This is a globally valid condition on every vertex: its active
            # normals cannot lie in a proper linear subspace. The new clause
            # forbids all models whose active normals lie in the current span.
            outside = [i for i, ee in enumerate(exps) if not in_span(ee, basis, pivots)]
            solver.add(z3.Or([eqs[i] for i in outside]))
            out["rank_cuts"] += 1
        else:
            assert value not in seen
            assert all(0 < x <= 1 for x in value)
            seen.add(value)
            full = [Fraction(0)]*chart.n
            for j, x in zip(free, value):
                full[j] = x
            independent = [active[i] for i in tags]
            cert = [exps[i] for i in independent]
            record = dict(weight=[str(x) for x in full],
                          active_exponents=[list(exps[i]) for i in active],
                          rank_certificate=dict(pivot_rows=independent, determinant=str(determinant(cert))))
            out["weights"].append(record)
            if progress:
                print("VERTEX", len(out["weights"]), ",".join(record["weight"]), "active", len(active), "det", record["rank_certificate"]["determinant"], flush=True)
            solver.add(z3.Or([x != z3.RealVal(str(y)) for x, y in zip(ww, value)]))
            if limit and len(out["weights"]) >= limit:
                out.update(termination="limit", reason=f"vertex limit {limit}")
                break
        now = time.monotonic()
        if progress and now-last >= 10:
            print("PROGRESS", "models", out["solver_models"], "rank_cuts", out["rank_cuts"], "vertices", len(out["weights"]), "seconds", round(now-start, 3), flush=True)
            last = now
    out["weights"].sort(key=lambda rr: tuple(Fraction(x) for x in rr["weight"]))
    out.update(full_vertex_count=len(out["weights"]), elapsed_seconds=time.monotonic()-start)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("d", type=int)
    parser.add_argument("--c", type=int, default=0)
    parser.add_argument("--s", type=int, default=1)
    parser.add_argument("--zero", default="", help="comma-separated valuation-zero names")
    parser.add_argument("--timeout", type=int, default=0, help="per exact Z3 check timeout, seconds; 0 means none")
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    zero = tuple(x for x in args.zero.split(",") if x)
    print("COMMAND", " ".join(sys.argv), flush=True)
    print("ENVIRONMENT", sys.version.replace("\n", " "), "z3", z3.get_version_string(), "seed", SEED, flush=True)
    out = enumerate_vertices(args.d, args.c, args.s, zero, args.timeout, args.limit)
    if args.output:
        args.output.write_text(json.dumps(out, indent=2)+"\n")
    print("SUMMARY", json.dumps({k:v for k,v in out.items() if k not in ("weights", "projected_exponents")}), flush=True)
    if not out["complete"]:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
