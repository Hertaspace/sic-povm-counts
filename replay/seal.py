#!/usr/bin/env python3
"""Rebuild publication byte bindings and the complete inventory, without mathematics."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def files():
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT)
        if any(part in {".git", "work", ".venv", "__pycache__"} for part in relative.parts):
            continue
        if path.is_file() and path.suffix != ".pyc":
            yield path, relative.as_posix()


def walk(value, pointer=""):
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, pointer + "/" + key.replace("~", "~0").replace("/", "~1"))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk(child, pointer + "/" + str(index))
    elif isinstance(value, str) and re.fullmatch("[0-9a-f]{64}", value):
        yield pointer, value


def main():
    provenance_path = ROOT / "provenance.json"
    provenance = json.loads(provenance_path.read_text())
    imported = {}
    original_index = {}
    for row in provenance["files"]:
        path = ROOT / row["path"]
        row["sha256"] = digest(path)
        row["bytes"] = path.stat().st_size
        if row["sha256"] != row["original_sha256"] and not row.get("changes"):
            row["changes"] = ["Privacy metadata normalization; mathematical payload retained."]
        imported[row["path"]] = row
        original_index.setdefault(row["original_sha256"], []).append(row)
    provenance_path.write_text(json.dumps(provenance, indent=2) + "\n")
    references = []
    for name in sorted(imported):
        if not name.endswith(".json"):
            continue
        for pointer, old in walk(json.loads((ROOT / name).read_text())):
            if old in original_index:
                references.append({"record": name, "pointer": pointer, "original_sha256": old,
                                   "published_bindings": [{"path": r["path"], "sha256": r["sha256"]}
                                                          for r in original_index[old]]})
    bindings = {
        "schema": "publication-byte-bindings-v1",
        "kind": "byte-correspondence-only",
        "mathematics_replayed": False,
        "historical_success_fields_are_new_acceptance": False,
        "provenance_sha256": digest(provenance_path),
        "explanation": "Embedded historical hashes retain their original meaning. These new bindings connect the selected original bytes to the adapted published bytes. A new mathematical replay must bind its own inputs and outputs.",
        "references": references,
    }
    (ROOT / "replay/bindings.json").write_text(json.dumps(bindings, indent=2) + "\n")
    archive = ROOT / "release/d7-root-certificates.tar.zst"
    attachment = json.loads((ROOT / "release/attachment.json").read_text())
    if digest(archive) != attachment["sha256"]:
        raise ValueError("attachment changed; regenerate its metadata explicitly")
    inventory = list(files())
    names = {name for _, name in inventory} | {"MANIFEST.md", "SHA256SUMS"}
    lines = [
        "# File manifest", "",
        "Author: Yaoling Yang. This is a publication inventory, not a new proof acceptance record.", "",
        "Every payload and source file is listed below. Neutral source locators identify the private selection without exposing private directory names. Original and published hashes record every adaptation; `provenance.json` is the machine-readable equivalent for imported files. New byte bindings are in `replay/bindings.json`. Historical success fields and their embedded hashes describe the original execution, never a fresh execution of edited code.", "",
        "`Repository` files belong in git. `Release` members belong to the ignored certificate attachment and are restored at the listed paths. The attachment itself is also ignored. Generated replay outputs, virtual environments, interpreter caches, and git internals are outside the publication inventory.", "",
        "A file cannot contain its own SHA-256. This manifest is hashed by `SHA256SUMS`; that index lists every other publication file, including the attachment and restored members, and omits only itself. Both index files are listed here. A git commit binds the index itself.", "",
        "| Published path | Source locator | Storage | Original bytes | Original SHA-256 | Published bytes | Published SHA-256 |",
        "|---|---|---|---:|---|---:|---|",
    ]
    for name in sorted(names):
        path = ROOT / name
        row = imported.get(name, {})
        store = "Release" if row.get("storage", "").startswith("Release") or name == archive.relative_to(ROOT).as_posix() else "Repository"
        if name == "MANIFEST.md":
            size, sha = "self", "See SHA256SUMS"
        elif name == "SHA256SUMS":
            size, sha = "index", "Self omitted; bound by git commit"
        else:
            size, sha = path.stat().st_size, digest(path)
        lines.append(f"| `{name}` | {row.get('source', 'New publication file')} | {store} | {row.get('original_bytes', '—')} | {row.get('original_sha256', '—')} | {size} | {sha} |")
    (ROOT / "MANIFEST.md").write_text("\n".join(lines) + "\n")
    sums = [digest(path) + "  " + name for path, name in files() if name != "SHA256SUMS"]
    (ROOT / "SHA256SUMS").write_text("\n".join(sums) + "\n")
    print(json.dumps({"imported_files": len(imported), "inventory_files": len(sums) + 1,
                      "rebound_historical_references": len(references), "mathematics_replayed": False}))


if __name__ == "__main__":
    main()
