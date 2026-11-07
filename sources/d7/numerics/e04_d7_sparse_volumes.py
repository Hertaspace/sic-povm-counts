#!/usr/bin/env python3.14
"""Remote exact shared-support volume upper certificates for gated d7 faces.

Each weight receives its own independently replayable certificate. Large
certificates are split into small aligned facet chunks, never >1 MiB files.
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
SEED = 20261102
TAGS = ("q", "l1", "l2", "z", "x1", "x2")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_small(path, data):
    payload = json.dumps(data, separators=(",", ":"))+"\n"
    assert len(payload.encode()) < 1024*1024, f"oversize file {path}"
    path.write_text(payload)
    return dict(file=path.name, bytes=path.stat().st_size, sha256=digest(path))


def save_certificate(path, record):
    encoded = json.dumps(record, separators=(",", ":"))+"\n"
    if len(encoded.encode()) < 1024*1024:
        return write_small(path, record)
    cert = dict(record["certificate"])
    simplices, normals = cert.pop("simplices"), cert.pop("facet_normals")
    parts = []
    for offset in range(0, len(simplices), 1000):
        part_path = path.with_name(path.stem+f"_part{len(parts):03d}.json")
        payload = dict(offset=offset, simplices=simplices[offset:offset+1000],
                       facet_normals=normals[offset:offset+1000])
        parts.append(write_small(part_path, payload))
    manifest = dict(record)
    manifest["certificate"] = cert
    manifest["facet_parts"] = parts
    return write_small(path, manifest)


def load_certificate(path):
    record = json.loads(path.read_text())
    if "facet_parts" in record:
        cert = record["certificate"]
        cert["simplices"], cert["facet_normals"] = [], []
        for part in record["facet_parts"]:
            pp = path.parent/part["file"]
            assert digest(pp) == part["sha256"]
            payload = json.loads(pp.read_text())
            assert payload["offset"] == len(cert["simplices"])
            cert["simplices"].extend(payload["simplices"])
            cert["facet_normals"].extend(payload["facet_normals"])
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate", type=Path, default=ROOT/"e14_calibration_gate.json")
    parser.add_argument("--tags", default=",".join(TAGS))
    parser.add_argument("--output-dir", type=Path, default=ROOT)
    parser.add_argument("--replay", type=Path)
    args = parser.parse_args()
    from e02_sparse_volume import verify_certificate
    if args.replay:
        report = json.loads(args.replay.read_text())
        for row in report["weights"]:
            path = args.replay.parent/row["certificate_file"]
            record = load_certificate(path)
            result = verify_certificate(record["certificate"])
            assert result == record["result"] == row["volume_result"]
            print("VERIFIED", row["tag"], row["index"], json.dumps(result), flush=True)
        print("ALL VERIFIED", len(report["weights"]), flush=True)
        return 0
    gate = json.loads(args.gate.read_text())
    assert gate["all_pass"] is True and gate["d6_boundary_total"] == 129024
    tags = args.tags.split(",")
    assert all(tag in TAGS for tag in tags) and len(set(tags)) == len(tags)
    import numpy as np
    import scipy
    from e02_sparse_volume import propose_certificate
    from e10_face_system import build_chart, face_at
    start = time.monotonic()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    report_path = args.output_dir/"e04_d7_sparse_volumes.json"
    report = dict(format="sic-nf6-d7-volume-upper-v1", seed=SEED,
        gate_sha256=digest(args.gate), host="not-recorded", python=sys.version,
        numpy=np.__version__, scipy=scipy.__version__, weights=[], status="RUNNING",
        sources_sha256={name:digest(ROOT/name) for name in
            ("e04_d7_sparse_volumes.py", "e02_sparse_volume.py", "e10_face_system.py")},
        interpretation="exact normalized shared-support volumes bound isolated torus roots from above; correlated coefficients do not imply equality")
    print("PROVENANCE", json.dumps(report, sort_keys=True), flush=True)
    write_small(report_path, report)
    for tag in tags:
        source_path = ROOT/f"e03_d7_{tag}.json"
        source = json.loads(source_path.read_text())
        assert source["d"] == 7 and source["complete"] is True and source["termination"] == "unsat"
        assert source["calibration_gate"]["gate_sha256"] == report["gate_sha256"]
        chart = build_chart(7, source["c"], source["s"])
        for index, vertex in enumerate(source["weights"]):
            print("BEGIN", tag, index, ",".join(vertex["weight"]), flush=True)
            face = face_at(chart, vertex["weight"])
            certificate, result = propose_certificate(face.support)
            record = dict(format="sic-exact-boundary-volume-certificate-v1",
                tag=tag, index=index, weight=vertex["weight"], names=list(chart.names),
                vertex_sha256=digest(source_path), certificate=certificate, result=result)
            cert_path = args.output_dir/f"e04_d7_{tag}_w{index:02d}_volume.json"
            artifact = save_certificate(cert_path, record)
            # Immediately replay the persisted artifact, including any chunks.
            persisted = load_certificate(cert_path)
            assert verify_certificate(persisted["certificate"]) == result
            row = dict(tag=tag, index=index, weight=vertex["weight"],
                certificate_file=artifact["file"], certificate_sha256=artifact["sha256"],
                certificate_bytes=artifact["bytes"], volume_result=result)
            report["weights"].append(row)
            write_small(report_path, report)
            print("RESULT", json.dumps(row, sort_keys=True), flush=True)
    report.update(status="PASS", elapsed_seconds=time.monotonic()-start)
    write_small(report_path, report)
    print("SUMMARY", json.dumps(dict(status=report["status"], weights=len(report["weights"]),
        seconds=report["elapsed_seconds"], report=report_path.name)), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
