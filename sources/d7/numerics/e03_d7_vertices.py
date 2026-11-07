#!/usr/bin/env python3.14
"""Run six exact d7 direct-face covers only after the saved d4–6 gate passes.

Preparation does not authorize execution. The coordinator launches this only
on the remote cluster, after separately confirming e14 all_pass.
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
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
REPRESENTATIVES = {
    "q": dict(c=0, s=1, zero_names=()),
    "l1": dict(c=0, s=1, zero_names=("b2",)),
    "l2": dict(c=0, s=1, zero_names=("b3",)),
    "z": dict(c=0, s=2, zero_names=("a1", "b3")),
    "x1": dict(c=0, s=1, zero_names=("b2", "b4")),
    "x2": dict(c=0, s=1, zero_names=("b2", "b3")),
}


def sha256_file(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", type=Path, default=ROOT/"e14_calibration_gate.json")
    parser.add_argument("--output-dir", type=Path, default=ROOT)
    parser.add_argument("--tags", default=",".join(REPRESENTATIVES))
    parser.add_argument("--timeout", type=int, default=0,
                        help="per exact Z3 check timeout in seconds; zero is unlimited")
    args = parser.parse_args()
    start = time.monotonic()
    gate_bytes = args.gate.read_bytes()
    gate = json.loads(gate_bytes)
    if gate.get("format") != "sic-nf6-calibration-gate-v1" or gate.get("all_pass") is not True:
        raise SystemExit("REFUSED: d4–6 calibration gate has not passed")
    if gate.get("d6_boundary_total") != 129024:
        raise SystemExit("REFUSED: saved gate lacks the d6 boundary closure")
    tags = args.tags.split(",")
    if len(set(tags)) != len(tags) or any(tag not in REPRESENTATIVES for tag in tags):
        raise SystemExit("invalid representative list")
    # Importing the exact backend occurs only after the gate is accepted.
    import z3
    from e01_gridless_vertices import enumerate_vertices
    gate_sha = hashlib.sha256(gate_bytes).hexdigest()
    provenance = dict(gate_file=args.gate.name, gate_sha256=gate_sha,
                      driver_sha256=sha256_file(Path(__file__)),
                      enumerator_sha256=sha256_file(ROOT/"e01_gridless_vertices.py"),
                      face_backend_sha256=sha256_file(ROOT/"e10_face_system.py"),
                      runtime_host="not-recorded", runtime_python=sys.version,
                      runtime_z3=z3.get_version_string())
    print("GATE", json.dumps(provenance, sort_keys=True), flush=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    summary = []
    all_complete = True
    for tag in tags:
        spec = REPRESENTATIVES[tag]
        print("BEGIN", tag, json.dumps(spec), flush=True)
        result = enumerate_vertices(7, timeout=args.timeout, **spec)
        result.update(representative=tag, calibration_gate=provenance)
        target = args.output_dir/f"e03_d7_{tag}.json"
        payload = json.dumps(result, indent=2)+"\n"
        if len(payload.encode()) > 1024*1024:
            raise RuntimeError(f"{tag} result exceeds the sync size limit; retain it under the task data directory")
        target.write_text(payload)
        row = dict(tag=tag, file=target.name, sha256=sha256_file(target),
                   candidate_count=result["full_vertex_count"], complete=result["complete"],
                   termination=result["termination"], rank_cuts=result["rank_cuts"],
                   elapsed_seconds=result["elapsed_seconds"])
        summary.append(row)
        all_complete = all_complete and result["complete"]
        print("END", json.dumps(row, sort_keys=True), flush=True)
    print("SUMMARY", json.dumps(dict(all_complete=all_complete,
          gate_sha256=gate_sha, runtime_z3=z3.get_version_string(), representatives=summary,
          elapsed_seconds=time.monotonic()-start), sort_keys=True), flush=True)
    return 0 if all_complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
