"""Compare the inputs recorded by the clean replay with the published tree."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
CLAIMS = ["integrity", "d4", "d5", "d6", "d7-finiteness", "d7-faces", "d7-spurious", "d7-orbits", "ghosts"]


def load(claim):
    path = HERE / claim / "result.json"
    if path.is_file():
        return json.loads(path.read_text())
    return json.loads(gzip.decompress((HERE / claim / "result.json.gz").read_bytes()))


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    records = {claim: load(claim) for claim in CLAIMS}
    trees = {r["source_tree_sha256"] for r in records.values()}
    if len(trees) != 1 or any(r["status"] != "PASS" for r in records.values()):
        raise SystemExit("records disagree on the source tree or did not pass")
    inputs = {row["path"]: row["sha256"] for row in records["d4"]["source_inputs"]}
    for claim, r in records.items():
        if {row["path"]: row["sha256"] for row in r["source_inputs"]} != inputs:
            raise SystemExit("input list differs in " + claim)
    missing = sorted(p for p in inputs if not (ROOT / p).is_file())
    release = [p for p in missing if p.startswith("release/") or p.startswith("sources/d7/numerics/e41_d7_cert_")]
    if release:
        raise SystemExit(f"{len(release)} release files are absent: download the attachment and run replay/restore_release.py first")
    changed = sorted(p for p, h in inputs.items() if not (ROOT / p).is_file() or sha256(ROOT / p) != h)
    published = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*")
                 if p.is_file() and not {".git", "work", "__pycache__"} & set(p.relative_to(ROOT).parts)
                 and p.name != ".DS_Store" and not p.name.endswith((".pyc", ".pyo"))}
    added = sorted(p for p in published - set(inputs) if not p.startswith("replay/clean-run/"))
    report = {
        "source_tree_sha256": trees.pop(),
        "recorded_inputs": len(inputs),
        "identical": len(inputs) - len(changed),
        "changed": changed,
        "added_outside_clean_run": added,
    }
    text = json.dumps(report, indent=2) + "\n"
    target = HERE / "tree-diff.json"
    if "--write" in sys.argv[1:]:
        target.write_text(text)
    elif target.read_text() != text:
        raise SystemExit("tree-diff.json does not match the current tree")
    print(text, end="")


if __name__ == "__main__":
    main()
