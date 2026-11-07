#!/usr/bin/env python3.14
"""Propose a sparse volume with Qhull, then verify its boundary exactly.

The certificate verifier uses only Python integer/Fraction arithmetic. Qhull
is an untrusted source of a simplicial boundary. The certificate proves its
normalized volume without assuming genericity of the equation coefficients.
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
from collections import defaultdict, deque
from fractions import Fraction
from functools import reduce
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import random
import sys
import time

sys.dont_write_bytecode = True
SEED = 20261102


def det_integer(rows):
    """Fraction-free Bareiss determinant with exact divisibility checks."""
    n = len(rows)
    if not n:
        return 1
    mat = [list(map(int, rr)) for rr in rows]
    sign, previous = 1, 1
    for k in range(n-1):
        pp = next((i for i in range(k, n) if mat[i][k]), None)
        if pp is None:
            return 0
        if pp != k:
            mat[k], mat[pp] = mat[pp], mat[k]
            sign = -sign
        pivot = mat[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                num = pivot*mat[i][j] - mat[i][k]*mat[k][j]
                assert num % previous == 0
                mat[i][j] = num//previous
            mat[i][k] = 0
        previous = pivot
    return sign*mat[-1][-1]


def primitive_normal(normal):
    den = lcm(*(x.denominator for x in normal))
    vv = [int(x*den) for x in normal]
    gg = reduce(gcd, map(abs, vv))
    if not gg:
        return None
    vv = [x//gg for x in vv]
    if next(x for x in vv if x) < 0:
        vv = [-x for x in vv]
    return tuple(vv)


def dot(xx, yy):
    return sum(x*y for x, y in zip(xx, yy))


def cofactor_normal(differences):
    n = len(differences[0])
    out = []
    for j in range(n):
        minor = [[row[k] for k in range(n) if k != j] for row in differences]
        out.append((-1)**j*det_integer(minor))
    return tuple(out)


def recover_normal(equation, vertices):
    """Recover an integer plane, then verify its kernel exactly."""
    vv = equation[:-1]
    j = max(range(len(vv)), key=lambda k: abs(vv[k]))
    for bound in (10, 100, 1000, 10000, 1000000):
        nn = primitive_normal(tuple(Fraction(float(x/vv[j])).limit_denominator(bound) for x in vv))
        if nn is not None:
            hh = dot(nn, vertices[0])
            if all(dot(nn, x) == hh for x in vertices):
                return nn
    dd = [[x-y for x, y in zip(vv, vertices[0])] for vv in vertices[1:]]
    return primitive_normal(tuple(Fraction(x) for x in cofactor_normal(dd)))


def boundary_orientation(simplices):
    """An oriented closed simplicial chain, checked over the integers."""
    ridges = defaultdict(list)
    for i, ss in enumerate(simplices):
        assert len(ss) == len(set(ss))
        for k in range(len(ss)):
            ridges[tuple(ss[:k]+ss[k+1:])].append((i, k))
    assert all(len(vv) == 2 for vv in ridges.values()), "non-manifold ridge incidence"
    adjacent = defaultdict(list)
    for vv in ridges.values():
        (i, ki), (j, kj) = vv
        factor = -((-1)**(ki+kj))
        adjacent[i].append((j, factor))
        adjacent[j].append((i, factor))
    orientation = [0]*len(simplices)
    orientation[0] = 1
    queue = deque([0])
    while queue:
        i = queue.popleft()
        for j, factor in adjacent[i]:
            value = orientation[i]*factor
            if orientation[j]:
                assert orientation[j] == value, "inconsistent boundary orientation"
            else:
                orientation[j] = value
                queue.append(j)
    assert all(orientation), "disconnected boundary complex"
    return orientation, len(ridges)


def solve_square(matrix, rhs):
    mm = [[Fraction(x) for x in row]+[Fraction(v)] for row, v in zip(matrix, rhs)]
    n = len(mm)
    for j in range(n):
        pp = next((i for i in range(j, n) if mm[i][j]), None)
        if pp is None:
            raise ValueError("singular simplex")
        mm[j], mm[pp] = mm[pp], mm[j]
        scale = mm[j][j]
        mm[j] = [x/scale for x in mm[j]]
        for i in range(n):
            if i != j and mm[i][j]:
                scale = mm[i][j]
                mm[i] = [x-scale*y for x, y in zip(mm[i], mm[j])]
    return [rr[-1] for rr in mm]


def simplex_membership(points, simplex, target, normal):
    omit = next(j for j, x in enumerate(normal) if x)
    n = len(normal)
    matrix = [[1]*n]+[[points[i][j] for i in simplex] for j in range(n) if j != omit]
    rhs = [Fraction(1)]+[target[j] for j in range(n) if j != omit]
    bary = solve_square(matrix, rhs)
    assert all(sum(b*points[i][j] for b, i in zip(bary, simplex)) == target[j] for j in range(n))
    if not all(b >= 0 for b in bary):
        return "outside"
    return "interior" if all(b > 0 for b in bary) else "boundary"


def verify_certificate(cert):
    points = [tuple(map(int, x)) for x in cert["points"]]
    simplices = [list(map(int, x)) for x in cert["simplices"]]
    n = len(points[0])
    assert len(cert["facet_normals"]) == len(simplices)
    assert n >= 2 and all(len(x) == n for x in points)
    assert len(set(points)) == len(points)
    assert all(ss == sorted(ss) and len(ss) == n for ss in simplices)
    assert len(set(tuple(ss) for ss in simplices)) == len(simplices)
    assert all(0 <= i < len(points) for ss in simplices for i in ss)
    orientation, ridge_count = boundary_orientation(simplices)
    total = [sum(x[j] for x in points) for j in range(n)]
    denominator = len(points)
    planes, plane_of, signed_cones = {}, [], []
    nondegenerate, degenerate = [], []
    for i, (ss, raw_normal) in enumerate(zip(simplices, cert["facet_normals"])):
        verts = [points[j] for j in ss]
        dd = [[x-y for x, y in zip(vv, verts[0])] for vv in verts[1:]]
        if raw_normal is None:
            assert not any(cofactor_normal(dd)), "unjustified degenerate simplex"
            signed_cones.append(Fraction(0))
            plane_of.append(None)
            degenerate.append(i)
            continue
        nn = tuple(map(int, raw_normal))
        assert len(nn) == n and any(nn)
        assert primitive_normal(tuple(Fraction(x) for x in nn)) == nn
        hh = dot(nn, verts[0])
        assert all(dot(nn, v) == hh for v in verts)
        j = next(k for k, x in enumerate(nn) if x)
        minor = det_integer([[row[k] for k in range(n) if k != j] for row in dd])
        if minor == 0:
            assert not any(cofactor_normal(dd))
            signed_cones.append(Fraction(0))
            plane_of.append(None)
            degenerate.append(i)
            continue
        height_num = hh*denominator-dot(nn, total)
        assert height_num != 0
        side = 1 if height_num > 0 else -1
        assert all(side*(hh-dot(nn, v)) >= 0 for v in points), "plane not supporting"
        plane = (*nn, hh)
        planes.setdefault(plane, []).append(i)
        plane_of.append(plane)
        scale = Fraction((-1)**j*minor, nn[j])
        cone = scale*Fraction(height_num, denominator)
        signed_cones.append(cone)
        nondegenerate.append(i)
    assert nondegenerate
    sign = 1 if orientation[nondegenerate[0]]*signed_cones[nondegenerate[0]] > 0 else -1
    orientation = [sign*x for x in orientation]
    assert all(orientation[i]*signed_cones[i] > 0 for i in nondegenerate), "folded or overlapping orientation"
    # Closed, outward, supporting boundary chain has a constant nonnegative
    # integer multiplicity on the connected boundary of conv(points). A test
    # point avoiding the simplex ridges fixes that multiplicity at one.
    target = tuple(Fraction(x) for x in cert["coverage_target"])
    containing, boundary_hits = [], []
    for plane, indices in planes.items():
        nn, hh = plane[:-1], plane[-1]
        if dot(nn, target) != hh:
            continue
        for i in indices:
            member = simplex_membership(points, simplices[i], target, nn)
            if member == "interior":
                containing.append(i)
            elif member == "boundary":
                boundary_hits.append(i)
    assert len(containing) == 1 and not boundary_hits, (containing, boundary_hits)
    volume = sum(abs(x) for x in signed_cones)
    assert volume.denominator == 1
    return dict(dimension=n, support_count=len(points), simplices=len(simplices),
                nondegenerate_simplices=len(nondegenerate), degenerate_simplices=len(degenerate),
                supporting_planes=len(planes), ridges=ridge_count,
                coverage_multiplicity=1, normalized_volume=int(volume),
                certificate_verified=True)


def propose_certificate(points):
    import numpy as np
    from scipy.spatial import ConvexHull
    points = [tuple(map(int, p)) for p in points]
    hull = ConvexHull(np.array(points, dtype=np.float64))
    pairs = sorted((tuple(sorted(map(int, ss))), eq) for ss, eq in zip(hull.simplices, hull.equations))
    simplices = [list(ss) for ss, _ in pairs]
    normals = [recover_normal(eq, [points[j] for j in ss]) for ss, eq in pairs]
    groups = defaultdict(list)
    for i, (ss, nn) in enumerate(zip(simplices, normals)):
        if nn is not None:
            groups[(*nn, dot(nn, points[ss[0]]))].append(i)
    target_simplex = min(groups.values(), key=lambda v: (len(v), v))[0]
    rand = random.Random(SEED)
    for trial in range(50):
        ss = simplices[target_simplex]
        weights = [1]*len(ss) if trial == 0 else [rand.randrange(1, 1001) for _ in ss]
        denom = sum(weights)
        target = [sum(w*points[i][j] for w, i in zip(weights, ss))/Fraction(denom) for j in range(len(points[0]))]
        cert = dict(points=[list(p) for p in points], simplices=simplices,
                    facet_normals=[list(nn) if nn is not None else None for nn in normals],
                    coverage_target=[str(x) for x in target], qhull_options="default Qt",
                    qhull_float_volume=float(hull.volume))
        try:
            summary = verify_certificate(cert)
            return cert, summary
        except AssertionError as err:
            if "[" not in str(err):
                raise
    raise RuntimeError("could not choose a coverage target avoiding all simplex ridges")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--output", type=Path, default=Path("e02_volume_calibrations.json"))
    parser.add_argument("inputs", nargs="*", type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    if args.verify:
        data = json.loads(args.verify.read_text())
        for row in data["cases"]:
            result = verify_certificate(row["certificate"])
            assert result == row["result"]
            print("VERIFIED", row["case"], row["weight"], json.dumps(result), flush=True)
        print("ALL VERIFIED", "seconds", time.monotonic()-start, flush=True)
        return
    from e10_face_system import build_chart, face_at
    import numpy as np
    import scipy
    print("ENVIRONMENT", sys.version.replace("\n", " "), "numpy", np.__version__,
          "scipy", scipy.__version__, "seed", SEED, flush=True)
    inputs = args.inputs or [Path(x) for x in ("e01_d4_point.json", "e01_d5_point.json", "e01_d5_line.json",
                 "e01_d6_point.json", "e01_d6_line.json", "e01_d6_surface.json", "e01_d6_line_a.json")]
    cases = []
    for path in inputs:
        data = json.loads(path.read_text())
        assert data["complete"] and data["d"] <= 6
        chart = build_chart(data["d"], data["c"], data["s"])
        for row in data["weights"]:
            face = face_at(chart, row["weight"])
            cert, result = propose_certificate(face.support)
            cases.append(dict(case=path.stem, weight=row["weight"], certificate=cert, result=result))
            print("RESULT", path.stem, ",".join(row["weight"]), json.dumps(result), flush=True)
    out = dict(format="sic-shared-support-volume-v1", seed=SEED, python=sys.version,
               numpy=np.__version__, scipy=scipy.__version__,
               elapsed_seconds=time.monotonic()-start, cases=cases,
               interpretation="normalized volume is an upper bound on isolated torus roots for all equations supported here; no generic-coefficient equality is assumed")
    args.output.write_text(json.dumps(out, separators=(",", ":"))+"\n")
    print("CERTIFICATE", str(args.output), "bytes", args.output.stat().st_size,
          "sha256", hashlib.sha256(args.output.read_bytes()).hexdigest(), flush=True)


if __name__ == "__main__":
    main()
