#!/usr/bin/env python3
"""Restore only the frozen certificate members, checking every byte hash."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    root = Path(__file__).resolve().parents[1]
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("archive", nargs="?", type=Path,
                    default=root / "release/d7-root-certificates.tar.zst")
    args = ap.parse_args()
    expected = json.loads((root / "release/attachment.json").read_text())
    if digest(args.archive) != expected["sha256"]:
        raise ValueError("attachment checksum mismatch")
    snapshot = json.loads((root / "sources/d7/numerics/e44_d7_second_batch_v1_root_snapshot.json").read_text())
    chunks = {"sources/d7/numerics/" + c["file"]: c for c in snapshot["chunks"]}
    seen = set()
    proc = subprocess.Popen(["zstd", "-dc", str(args.archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for item in archive:
                if not item.isfile() or item.name not in chunks or item.name in seen:
                    raise ValueError("unexpected attachment member: " + item.name)
                seen.add(item.name)
                chunk = chunks[item.name]
                data = archive.extractfile(item).read()
                if hashlib.sha256(data).hexdigest() != chunk["sha256"]:
                    raise ValueError("member checksum mismatch: " + item.name)
                destination = root / item.name
                if destination.exists():
                    if digest(destination) != chunk["sha256"]:
                        raise FileExistsError("refusing to overwrite differing input: " + item.name)
                else:
                    if destination.parent.is_symlink() or any(p.is_symlink() for p in destination.parents):
                        raise ValueError("refusing a symbolic-link destination")
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    with destination.open("xb") as stream:
                        stream.write(data)
        if proc.wait() != 0 or seen != set(chunks):
            raise ValueError("incomplete attachment")
    finally:
        if proc.poll() is None:
            proc.kill()
        proc.wait()
    print(json.dumps({"restored_or_verified_members": len(seen), "input_integrity_only": True}))


if __name__ == "__main__":
    main()
