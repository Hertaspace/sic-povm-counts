#!/usr/bin/env python3
"""Exact normalized volume of the direct-face Newton polytope.

n! Vol(conv A) is the Kushnirenko upper bound on isolated torus roots.
The triangulation is a placing triangulation with exact integer determinants.
Qhull is not used.
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

from fractions import Fraction

import k1_face as K


def idet(rows):
    n = len(rows)
    M = [[Fraction(x) for x in row] for row in rows]
    det = Fraction(1)
    for i in range(n):
        piv = None
        for k in range(i, n):
            if M[k][i] != 0:
                piv = k
                break
        if piv is None:
            return 0
        if piv != i:
            M[i], M[piv] = M[piv], M[i]
            det = -det
        det *= M[i][i]
        inv = M[i][i]
        for k in range(i + 1, n):
            if M[k][i] == 0:
                continue
            factor = M[k][i] / inv
            for j in range(i, n):
                M[k][j] -= factor * M[i][j]
    if det.denominator != 1:
        raise RuntimeError(f"nonintegral det {det}")
    return int(det.numerator)


def facet_det(points, facet, extra):
    base = points[facet[0]]
    rows = []
    for idx in facet[1:]:
        rows.append([points[idx][j] - base[j] for j in range(len(base))])
    rows.append([points[extra][j] - base[j] for j in range(len(base))])
    return idet(rows)


def simplex_volume(points, idxs):
    """Absolute determinant of the n edges of an n-simplex. Equals n! Vol."""
    return abs(facet_det(points, idxs[:-1], idxs[-1]))


def placing_volume(raw_points):
    points = sorted(set(tuple(p) for p in raw_points))
    if not points:
        return {"n_points": 0, "normalized_volume": 0}
    n = len(points[0])
    # initial simplex
    chosen = [0]
    for i in range(1, len(points)):
        trial = chosen + [i]
        if len(trial) <= n:
            # rank of edge matrix
            base = points[trial[0]]
            rows = [[points[k][j] - base[j] for j in range(n)] for k in trial[1:]]
            # pad to square with zeros and use a maximal minor via GE rank
            rank = _rank(rows, n)
            if rank == len(rows):
                chosen.append(i)
        else:
            if facet_det(points, chosen, i) != 0:
                chosen.append(i)
                break
    if len(chosen) < n + 1:
        return {
            "n_points": len(points),
            "affine_rank": len(chosen) - 1,
            "normalized_volume": None,
            "full_dimensional": False,
        }
    simplices = [tuple(chosen)]
    # facets: (vertex-index tuple length n, outside_sign)
    facets = []
    for omit in range(n + 1):
        facet = tuple(chosen[j] for j in range(n + 1) if j != omit)
        inside = facet_det(points, facet, chosen[omit])
        if inside == 0:
            raise RuntimeError("degenerate initial facet")
        outside = -1 if inside > 0 else 1
        facets.append((facet, outside))
    used = set(chosen)
    for i in range(len(points)):
        if i in used:
            continue
        visible = []
        for fi, (facet, outside) in enumerate(facets):
            d = facet_det(points, facet, i)
            if d == 0:
                continue
            if (1 if d > 0 else -1) == outside:
                visible.append(fi)
        if not visible:
            continue  # inside or on the boundary
        vis_set = set(visible)
        ridge_owner = {}
        for fi in visible:
            facet = facets[fi][0]
            for drop in range(n):
                ridge = tuple(facet[j] for j in range(n) if j != drop)
                key = frozenset(ridge)
                ridge_owner.setdefault(key, []).append((fi, ridge))
        horizon = [v[0] for v in ridge_owner.values() if len(v) == 1]
        new_simplices = []
        new_facets = []
        for fi in visible:
            facet = facets[fi][0]
            simp = facet + (i,)
            new_simplices.append(simp)
        for fi, ridge in horizon:
            # inside reference: a vertex of the old facet not on the ridge
            facet = facets[fi][0]
            ridge_set = set(ridge)
            interior_vertex = next(v for v in facet if v not in ridge_set)
            new_facet = ridge + (i,)
            inside = facet_det(points, new_facet, interior_vertex)
            if inside == 0:
                # new point coplanar with this ridge and the interior vertex;
                # should not happen for a strictly visible facet's horizon
                raise RuntimeError("flat new facet")
            outside = -1 if inside > 0 else 1
            new_facets.append((new_facet, outside))
        facets = [f for j, f in enumerate(facets) if j not in vis_set] + new_facets
        simplices.extend(new_simplices)
        used.add(i)
    # closed boundary: every ridge in exactly two facets
    ridge_count = {}
    for facet, _ in facets:
        for drop in range(n):
            ridge = frozenset(facet[j] for j in range(n) if j != drop)
            ridge_count[ridge] = ridge_count.get(ridge, 0) + 1
    bad = sum(1 for c in ridge_count.values() if c != 2)
    vol = sum(simplex_volume(points, s) for s in simplices)
    return {
        "n_points": len(points),
        "n_hull_points_used": len(used),
        "n_simplices": len(simplices),
        "n_facets": len(facets),
        "bad_ridges": bad,
        "normalized_volume": vol,
        "full_dimensional": True,
    }


def _rank(rows, n):
    M = [[Fraction(x) for x in row] for row in rows]
    rank = 0
    col = 0
    while rank < len(M) and col < n:
        piv = None
        for i in range(rank, len(M)):
            if M[i][col] != 0:
                piv = i
                break
        if piv is None:
            col += 1
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = M[rank][col]
        for j in range(col, n):
            M[rank][j] /= inv
        for i in range(len(M)):
            if i == rank or M[i][col] == 0:
                continue
            factor = M[i][col]
            for j in range(col, n):
                M[i][j] -= factor * M[rank][j]
        rank += 1
        col += 1
    return rank


def support_of(tag):
    w = K.parse_weight(K.CONES[tag])
    polys = K.sic_generators(K.build_all_q())
    _, mons = K.leading_parts(polys, w)
    p_mons = K.perturbation_monomials(w)
    return [tuple(m) for m in mons] + [tuple(m) for m in p_mons]


def self_test():
    # standard 2-simplex, normalized volume 1
    assert placing_volume([(0, 0), (1, 0), (0, 1)])["normalized_volume"] == 1
    # unit square, 2! Vol = 2
    assert placing_volume([(0, 0), (1, 0), (0, 1), (1, 1)])["normalized_volume"] == 2
    # interior point does not change the square
    assert placing_volume([(0, 0), (1, 0), (0, 1), (1, 1), (1, 1)])["normalized_volume"] == 2
    # unit cube, 3! Vol = 6
    cube = [(i, j, k) for i in (0, 1) for j in (0, 1) for k in (0, 1)]
    got = placing_volume(cube)
    assert got["normalized_volume"] == 6 and got["bad_ridges"] == 0, got
    # standard 12-simplex
    pts = [tuple(0 for _ in range(12))]
    for i in range(12):
        v = [0] * 12
        v[i] = 1
        pts.append(tuple(v))
    got = placing_volume(pts)
    assert got["normalized_volume"] == 1 and got["bad_ridges"] == 0, got
    print("volume self-test ok", flush=True)


def main():
    self_test()
    for tag in ("l1_72", "l1_16", "l2_128"):
        pts = support_of(tag)
        got = placing_volume(pts)
        got["tag"] = tag
        got["claimed"] = K.CLAIMED[tag]
        print(got, flush=True)


if __name__ == "__main__":
    main()
