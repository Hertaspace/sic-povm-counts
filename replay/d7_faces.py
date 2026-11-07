#!/usr/bin/env python3
"""Portable driver for twelve specified direct faces; no computation without --run.

The checker is supplied in independent/d7-faces/k1_face.py.
Listed weights use a0=b1=1 and (a1,...,a6,b0,b2,...,b6).
The z96 representative has been translated by one cyclic index into this chart.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

CONES = {
    "q576": ("1/2,1,1/3,1/4,3/4,2/3,1/2,2/3,3/4,1/4,1/3,1", 576),
    "q1968": ("1/2,1,1/3,5/6,1/6,2/3,1/2,2/3,1/6,5/6,1/3,1", 1968),
    "q640": ("1/2,1,5/8,1/4,3/4,3/8,1/2,3/8,3/4,1/4,5/8,1", 640),
    "q1000": ("1/2,1,4/5,3/5,2/5,1/5,1/2,1/5,2/5,3/5,4/5,1", 1000),
    "l1_48": ("1/2,1,1,1,1/2,1/2,1/2,0,1/2,1/2,1,1", 48),
    "l1_72": ("1/2,1,1,1,2/3,1/3,1/2,0,1/3,2/3,1,1", 72),
    "l1_16": ("1/2,1,1,1,3/4,3/4,1/2,0,3/4,1/4,1,1", 16),
    "l2_48": ("1/2,1,1/2,1,1/2,1,1/2,1/2,0,1,1/2,1", 48),
    "l2_128": ("3/4,1,1/2,1,1/4,1,1/2,3/4,0,1,1/4,1", 128),
    "x1_8": ("1,1,1,1,1,1,1/2,0,1,0,1,1", 8),
    "x2_32": ("1/2,1,1,1,1,1,1/2,0,0,1,1,1", 32),
    "z96": ("1/2,1,1,1,1,0,1/2,0,1,1,1,1", 96),
}


def require(value, message):
    if not value:
        raise ValueError(message)


def validate_reports(out, cones=None):
    cones = CONES if cones is None else cones
    summary = json.loads((out / "summary.json").read_text())
    require(summary["primes"] == [100003, 100129], "wrong face-audit primes")
    require(summary["matrix_vs_definition_mismatches"] == 0, "literal displacement definition mismatch")
    require(summary["q_rank_sic"]["rank"] == 15 and summary["q_rank_sic"]["monomials"] == 112
            and summary["q_rank_with_q00"] == 16 and summary["q_union_support_excluding_q00"] == 112,
            "wrong full equation span or support")
    require(set(summary["cones"]) == set(cones), "missing or unexpected face analyses")
    expected_pairs = {(p, s) for p in (100003, 100129) for s in (8675309, 42424249)}
    for tag, (weight, length) in cones.items():
        analysis = json.loads((out / (tag + "_analysis.json")).read_text())
        require(analysis == summary["cones"][tag], "analysis and global summary disagree: " + tag)
        require(analysis["tag"] == tag and analysis["claimed_length"] == length and analysis["weight"] == weight,
                "face weight or identity mismatch: " + tag)
        require(analysis["min_weight"] == "1" and analysis["min_weight_is_one"] is True
                and analysis["weights_below_one"] == [], "incorrect initial face: " + tag)
        require(analysis["exact_support_count"] == 112
                and set(analysis["primes"]) == {"100003", "100129"}, "incomplete face support analysis")
        for prime in analysis["primes"].values():
            require(prime["q_rank"] == 15 and prime["q_support_mod_p"] == 112
                    and prime["weight1_monomials_killed"] == 0, "equation terms lost after reduction: " + tag)
        report = json.loads((out / (tag + "_solve.json")).read_text())
        rows = [r for r in report if r["mode"] == "generic_12_plane"]
        require(len(rows) == 4 and {(r["p"], r["seed"]) for r in rows} == expected_pairs,
                "missing or repeated prime/seed pair: " + tag)
        for row in rows:
            require(row["claimed"] == length and row["dim_V"] == analysis["primes"][str(row["p"])]["dim_V"],
                    "solver used a different face family: " + tag)
            rur, stair = row["rur"], row["staircase"]
            require(rur["status"] == "finite" and rur["simple"] is True
                    and rur["scheme_length"] == rur["minpoly_degree"] == length,
                    "non-simple or wrong-degree parametrization: " + tag)
            require(stair["status"] == "zero_dimensional" and stair["length"] == length
                    and row["length_agree"] is True, "saturated length mismatch: " + tag)
            for key in ("rur_run", "gb_run"):
                require(row[key]["returncode"] == 0 and row[key]["killed"] is None, "solver did not finish: " + tag)


def main():
    require(__debug__, "Python optimization is not supported")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", action="store_true")
    ap.add_argument("--checker", type=Path, default=Path("independent/d7-faces/k1_face.py"))
    ap.add_argument("--checker-sha256", help="must match the final published checker bytes")
    ap.add_argument("--work", type=Path, default=Path("work/faces/work"))
    ap.add_argument("--out", type=Path, default=Path("work/faces/out"))
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--mem-gb", type=int, default=20)
    ap.add_argument("--timeout", type=int, default=20000)
    args = ap.parse_args()
    if not args.run:
        print(json.dumps({k: {"weight": w, "simple_torus_roots_lower_bound": n} for k, (w, n) in CONES.items()}, indent=2))
        return
    require(args.checker_sha256 and len(args.checker_sha256) == 64, "--checker-sha256 is required for execution")
    source = args.checker.resolve()
    require(hashlib.sha256(source.read_bytes()).hexdigest() == args.checker_sha256, "checker source hash mismatch")
    require(not args.work.exists() and not args.out.exists(), "choose fresh work and output directories")
    spec = importlib.util.spec_from_file_location("independent_face_checker", source)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.CONES = {k: w for k, (w, _) in CONES.items()}
    module.CLAIMED = {k: n for k, (_, n) in CONES.items()}
    sys.argv = [str(source), "--only", ",".join(CONES), "--prime-start", "100000", "--primes", "2",
                "--seeds", "8675309,42424249", "--solve", "--with-gb", "--threads", str(args.threads),
                "--mem-gb", str(args.mem_gb), "--timeout", str(args.timeout), "--work", str(args.work), "--out", str(args.out)]
    module.main()
    validate_reports(args.out)
    print(json.dumps({"accepted_face_runs": 48, "cones": 12, "higher_order_path_exhaustion_claimed": False}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print("CHECK FAILED: " + str(error), file=sys.stderr)
        raise SystemExit(1)
