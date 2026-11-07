#!/usr/bin/env python3
"""Strict acceptance checks used by the portable replay command.

These checks validate freshly produced reports when replay is run in execution
mode. With ``--records-only`` they validate historical report structure and
input provenance; that mode does not rerun the mathematics.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import re
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any


FROZEN_SNAPSHOT_SHA256 = "32ff7680408a594da91ea7ba16b9d880a01efb74080b616525c8ae62d37825f9"
CLAIM_INPUTS = {
    "d4": {"d4-count", "d4-d5-lower"},
    "d5": {"d5-count", "d5-escape", "d4-d5-lower"},
    "d6": {"d6"},
    "d7-finiteness": {"d7-finite"},
    "d7-faces": {"d7-faces-and-calibration", "d7-faces-independent",
                  "d7-faces-independent-summary-only", "d7-calibration-gate-inputs"},
    "d7-spurious": {"d7-spur", "d7-spur-frozen", "d7-spur-independent"},
    "d7-orbits": {"d7-orbits"},
    "ghosts": {"d4-count", "d4-d5-lower", "d5-count", "d5-escape", "d6",
               "d7-finite", "d7-orbits", "d7-spur-frozen", "d7-spur-independent"},
    "integrity": set(),
}


class AcceptanceError(ValueError):
    """Raised when a report is incomplete or fails an acceptance condition."""


def require(condition: Any, message: str) -> None:
    if not condition:
        raise AcceptanceError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def safe_relative_path(value: str) -> PurePosixPath:
    path = PurePosixPath(value.replace("\\", "/"))
    require(not path.is_absolute(), f"absolute path in public inventory: {value}")
    require(path.parts and all(part not in ("", ".", "..") for part in path.parts),
            f"unsafe path in public inventory: {value}")
    return path


def provenance_index(root: Path) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    path = root / "provenance.json"
    require(path.is_file(), "missing provenance.json")
    data = load_json(path)
    require(data.get("schema") == "public-evidence-provenance-v1", "unsupported provenance schema")
    files = data.get("files")
    require(isinstance(files, list) and files, "provenance.json has no file inventory")
    by_path: dict[str, dict[str, Any]] = {}
    for item in files:
        require(isinstance(item, dict), "malformed provenance file entry")
        rel = str(item.get("path", ""))
        safe_relative_path(rel)
        require(rel not in by_path, "duplicate provenance path: " + rel)
        current = item.get("sha256")
        original = item.get("original_sha256")
        require(isinstance(current, str) and re.fullmatch(r"[0-9a-f]{64}", current),
                "invalid public SHA-256: " + rel)
        require(isinstance(original, str) and re.fullmatch(r"[0-9a-f]{64}", original),
                "invalid original SHA-256: " + rel)
        by_path[rel] = item
    return by_path, data


def verify_provenance(root: Path, *, claim: str = "integrity",
                      include_unlisted: bool = True) -> dict[str, Any]:
    """Verify public source entries, with release artifacts required by claim.

    The provenance file binds publication bytes. ``original_sha256`` retains
    the source-byte reference for historical records; it is never substituted
    for the hash of a newly adapted program. Large release-only certificates
    are optional for ordinary claims, but integrity and d7-spurious require
    their materialization and archive binding.
    """
    root = Path(root).resolve()
    require(claim in CLAIM_INPUTS, "unknown claim for provenance verification")
    require_release = claim in {"integrity", "d7-spurious"}
    by_path, prov = provenance_index(root)
    release_paths = {rel for rel, item in by_path.items()
                     if str(item.get("storage", "")).startswith("Release:")}
    verified = []
    missing = []
    for rel, item in by_path.items():
        safe = safe_relative_path(rel)
        target = root.joinpath(*safe.parts)
        if not target.is_file():
            if require_release or rel not in release_paths:
                missing.append(rel)
            continue
        actual = sha256(target)
        require(actual == item["sha256"], f"publication-byte hash mismatch: {rel}")
        if "bytes" in item:
            require(target.stat().st_size == item["bytes"], f"publication-byte size mismatch: {rel}")
        verified.append(rel)
    require(not missing, "provenance paths are not materialized: " + ", ".join(missing[:8]))

    sums_path = root / "SHA256SUMS"
    sums_count = 0
    sum_paths: set[str] = set()
    if sums_path.is_file():
        for line_no, line in enumerate(sums_path.read_text(encoding="utf-8").splitlines(), 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            match = re.fullmatch(r"([0-9a-fA-F]{64})\s+[* ]?(.+)", line)
            require(match is not None, f"malformed SHA256SUMS line {line_no}")
            expected, rel = match.groups()
            safe = safe_relative_path(rel)
            target = root.joinpath(*safe.parts)
            sum_paths.add(rel)
            if not target.is_file():
                optional = rel in release_paths or PurePosixPath(rel).name == "d7-root-certificates.tar.zst"
                require(optional and not require_release,
                        "SHA256SUMS target missing: " + rel)
                continue
            require(sha256(target) == expected.lower(), "SHA256SUMS mismatch: " + rel)
            sums_count += 1

    archive_candidates = {rel for rel in sum_paths
                          if PurePosixPath(rel).name == "d7-root-certificates.tar.zst"}
    if require_release:
        require(release_paths, "provenance has no release-backed d7 root chunks")
        require(all((root / Path(*safe_relative_path(rel).parts)).is_file() for rel in release_paths),
                "d7 release-backed root chunks are not fully materialized")
        require(len(archive_candidates) == 1,
                "SHA256SUMS must bind exactly one d7 root-certificate archive")
        archive_path = root / Path(*safe_relative_path(next(iter(archive_candidates))).parts)
        require(archive_path.is_file(), "d7 root-certificate archive is missing")
    else:
        archive_path = None

    tree = inventory_tree(root) if include_unlisted else {}
    return {
        "schema": prov["schema"],
        "provenance_entries": len(by_path),
        "verified_public_files": len(verified),
        "sha256sums_entries": sums_count,
        "tree_files": len(tree),
        "provenance_sha256": sha256(root / "provenance.json"),
        "sha256sums_sha256": sha256(sums_path) if sums_path.is_file() else None,
        "release_artifacts_required": require_release,
        "release_files_verified": sum(1 for rel in release_paths if rel in verified),
        "release_archive_sha256": sha256(archive_path) if archive_path is not None else None,
        "verified": True,
    }


def inventory_tree(root: Path, *, include_work: bool = False) -> dict[str, dict[str, Any]]:
    """Hash the materialized repository tree, excluding VCS and run output."""
    root = Path(root).resolve()
    ignored_dirs = {".git", ".venv", "__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache"}
    if not include_work:
        ignored_dirs.add("work")
    result: dict[str, dict[str, Any]] = {}
    for current, dirs, names in __import__("os").walk(root):
        base = Path(current)
        for dirname in dirs:
            if dirname not in ignored_dirs:
                require(not (base / dirname).is_symlink(),
                        "symlinked input directory is not allowed: " + (base / dirname).relative_to(root).as_posix())
        dirs[:] = sorted(d for d in dirs if d not in ignored_dirs)
        for name in sorted(names):
            if name in {".DS_Store"} or name.endswith((".pyc", ".pyo")):
                continue
            target = base / name
            require(not target.is_symlink(),
                    "symlinked input file is not allowed: " + target.relative_to(root).as_posix())
            if not target.is_file():
                continue
            rel = target.relative_to(root).as_posix()
            result[rel] = {"sha256": sha256(target), "bytes": target.stat().st_size}
    return result


def claim_provenance(root: Path, claim: str) -> list[dict[str, Any]]:
    by_path, _ = provenance_index(root)
    wanted = CLAIM_INPUTS.get(claim, set())
    rows = []
    for rel, item in sorted(by_path.items()):
        claims = set(item.get("claims", []))
        if claim == "integrity" or claims & wanted:
            rows.append({
                "path": rel,
                "sha256": item["sha256"],
                "original_sha256": item["original_sha256"],
                "bytes": item.get("bytes"),
                "claims": sorted(claims),
            })
    return rows


def check_frozen_snapshot(path: Path, *, require_frozen_hash: bool = True) -> dict[str, Any]:
    path = Path(path)
    require(path.is_file(), "missing frozen d7 root snapshot: " + path.name)
    snapshot_hash = sha256(path)
    if require_frozen_hash:
        require(snapshot_hash == FROZEN_SNAPSHOT_SHA256, "wrong frozen d7 proof snapshot hash")
    snapshot = load_json(path)
    require(snapshot["d"] == 7, "snapshot dimension is not 7")
    require(snapshot["certified_representatives"] == 21232, "snapshot representative count is not 21232")
    require(snapshot.get("certified_points_before_orbit_dedup") == 2080736,
            "snapshot does not bind the full 2,080,736 point set")
    require(snapshot.get("free_orbit_size") == 98, "snapshot free orbit size is not 98")
    chunks = snapshot.get("chunks")
    require(isinstance(chunks, list) and len(chunks) == 886, "snapshot must have exactly 886 chunks")
    names: set[str] = set()
    ids: list[int] = []
    for row in chunks:
        name = row["file"]
        safe = safe_relative_path(name)
        require(len(safe.parts) == 1, "snapshot chunk name must be a basename")
        require(name not in names, "duplicate root chunk: " + name)
        names.add(name)
        require(row["count"] == len(row["ids"]), "chunk count disagrees with its ID list: " + name)
        target = path.parent / name
        require(target.is_file(), "missing frozen root chunk: " + name)
        require(sha256(target) == row["sha256"], "frozen root chunk SHA-256 mismatch: " + name)
        ids.extend(row["ids"])
    require(len(ids) == len(set(ids)) == 21232, "root chunk IDs are incomplete or repeated")
    header_name = snapshot["header_file"]
    require(len(safe_relative_path(header_name).parts) == 1, "unsafe header filename")
    header_path = path.parent / header_name
    require(header_path.is_file() and sha256(header_path) == snapshot["header_sha256"],
            "snapshot header binding failed")
    header = load_json(header_path)
    require(header["d"] == 7 and header["free_group_order"] == 98, "invalid snapshot header")
    matrix_name = header["matrix_file"]
    require(len(safe_relative_path(matrix_name).parts) == 1, "unsafe matrix filename")
    matrix_path = path.parent / matrix_name
    require(matrix_path.is_file() and sha256(matrix_path) == header["matrix_sha256"],
            "snapshot matrix binding failed")
    matrix = load_json(matrix_path)
    require(matrix["d"] == 7 and matrix["n"] == 12 and matrix["m"] == 24,
            "wrong d7 matrix shape")
    require(matrix["denominator"] == 2**32, "wrong d7 matrix denominator")
    require(len(matrix["q_labels"]) == 24, "incomplete d7 matrix label set")
    require(len(set(tuple(q) for q in matrix["q_labels"])) == 24, "repeated d7 matrix labels")
    return {
        "snapshot_sha256": snapshot_hash,
        "chunks": len(names),
        "representatives": len(ids),
        "certified_points_before_orbit_dedup": 2080736,
        "header_sha256": sha256(header_path),
        "matrix_sha256": sha256(matrix_path),
        "frozen_hash_checked": require_frozen_hash,
        "mathematics_replayed": False,
    }


def check_d7_orbits(report: dict[str, Any]) -> dict[str, Any]:
    exact = report["exact"]
    for key in ("unit_tests", "P_orthogonal", "P_order", "P_WT"):
        require(exact[key] is True, "exact orbit check failed: " + key)
    require(set(exact["seeds"]) == {"F1", "F2", "G1", "G2"}, "wrong exact seed set")
    for name, seed in exact["seeds"].items():
        require(seed["Z0_is_one"] is True and seed["Z0_zero"] is False and seed["n_reps"] == 24
                and seed["q_bad_count"] == seed["quartic_bad_count"] == 0,
                "exact seed equation failure: " + name)
        require(seed["fixed_by_P"] is True and seed["doubling_symmetry"] is True,
                "exact seed symmetry failure: " + name)
        require(seed["hermitian"] is (name in {"F1", "F2"}), "wrong Hermitian label: " + name)
    require(len(exact["covariance"]) == 4, "missing orbit generator checks")
    for row in exact["covariance"]:
        require(row["inverse_ok"] is True and row["chi_pair_ok"] is True and row["linear_11"] is True
                and row["unidentified"] == [] and row["det"] == 1 and row["n_images"] == 49,
                "generator covariance failure")
    pc = exact["P_clifford"]
    require(pc["unidentified"] == [] and pc["det"] == 1 and pc["trace"] == 6
            and pc["chi_pair_ok"] is True, "Zauner-label check failed")
    require(set(report["primes"]) == {"673", "953"}, "wrong orbit reduction-prime set")
    for prime, row in report["primes"].items():
        require(row["group_order"] == 16464 and row["union"] == 32928,
                "wrong group order or point count at " + prime)
        require(row["kernel"] == row["displacements_distinct"] == row["displacements_in_group"] == 49,
                "wrong displacement subgroup at " + prime)
        for key in ("sigma_fail", "chi_fail", "not_linear", "sl_missing", "sl_extra"):
            require(row[key] == 0, "group check failure: " + prime + ":" + key)
        require(row["n_symplectic_images"] == 336 and row["fibre_sizes"] == [49],
                "wrong symplectic quotient at " + prime)
        expected_reps = {"F1", "TF1", "F2", "G1", "TG1", "G2"}
        require({r["rep"] for r in row["ordinary_orbits"]} == expected_reps
                and len(row["ordinary_orbits"]) == 6, "wrong ordinary orbit set at " + prime)
        require(all(r["size"] == 5488 and r["overlap_previous"] == 0
                    for r in row["ordinary_orbits"]), "overlapping or wrong-sized orbit at " + prime)
        require(set(row["seeds"]) == {"F1", "F2", "G1", "G2"}, "missing modular seed at " + prime)
        for name, seed in row["seeds"].items():
            require(seed["stab"] == 3 and seed["orbit"] == 5488 and seed["wh_images"] == 49,
                    "wrong modular stabilizer at " + prime + ":" + name)
            require(len(seed["stab_sl"]) == 3
                    and sorted(s["trace"] for s in seed["stab_sl"]) == [2, 6, 6]
                    and all(s["det"] == 1 for s in seed["stab_sl"]),
                    "wrong modular stabilizer labels at " + prime + ":" + name)
            require(seed["T_in_orbit"] is (name in {"F2", "G2"}),
                    "wrong factor-swap orbit at " + prime + ":" + name)
        require(row["extended_family_sizes"] == {"F1": 10976, "F2": 5488, "G1": 10976, "G2": 5488},
                "wrong extended family sizes at " + prime)
    sg = exact["sg"]
    require(sg["r1_sq_ok"] is True and sg["r1_real"] is True, "reference radical identity failed")
    for label in ("7a", "7b"):
        row = sg[label]
        require(row["Z0_zero"] is False and row["n_reps"] == 24 and row["q_bad_count"] == 0
                and row["hermitian"] is True and row["doubling_symmetry"] is True
                and row["fixed_by_P"] is True, "reference projector check failed: " + label)
    expected_words = {"7a": "F1", "7aswap": "F1", "7b": "F2", "7bswap": "F2"}
    words = report["sg_words"]
    require(len(words) == 4 and {r["label"] for r in words} == set(expected_words)
            and all(r["exact_parallel"] is True and r["seed"] == expected_words[r["label"]]
                    for r in words), "reference-orbit identification failed")
    return {"group_orders": [16464, 32928], "ordinary_orbits_per_prime": 6,
            "extended_orbits_per_prime": 4, "reduction_primes": [673, 953],
            "report_fields_accepted": True}


def _require_json(path: Path, context: str) -> dict[str, Any]:
    require(path.is_file(), f"missing {context} report: {path.as_posix()}")
    value = load_json(path)
    require(isinstance(value, dict), f"{context} report is not a JSON object")
    return value


def check_d4_fiber_output(output: str) -> dict[str, Any]:
    required = {
        "CHART_DIM": 0,
        "CHART_LENGTH": 512,
        "TRACE_RELATION_REMAINDER": 0,
        "TRACE_ZERO_LENGTH": 256,
        "TRACE_ZERO_REDUCED": 1,
        "A_COMPLEMENT_UNIT": 1,
        "B_COMPLEMENT_UNIT": 1,
    }
    got = {}
    for key, expected in required.items():
        match = re.search(rf"^{key}=(-?\d+)$", output, flags=re.M)
        require(match is not None, "d4 open-fibre output lacks " + key)
        got[key] = int(match.group(1))
        require(got[key] == expected, f"d4 open-fibre {key}={got[key]}, expected {expected}")
    require(not re.search(r"^\s*\?", output, flags=re.M), "Singular reported an error in d4 open fibre")
    return got


def check_d4_boundary(path: Path, characteristic: int) -> dict[str, Any]:
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    require(f"CASE d=4 p={characteristic} " in text, "d4 boundary report has the wrong case")
    require(re.search(r"^EXIT=0\b", text, flags=re.M) is not None, "d4 boundary process failed")
    require(not re.search(r"^\s*\?", text, flags=re.M), "Singular reported an error in d4 boundary run")
    require(len(re.findall(r"^FULL_CHART \d \d DIM_LENGTH: 0 \d+$", text, flags=re.M)) == 16,
            "d4 boundary report does not cover all 16 full charts")
    require(len(re.findall(r"^TRACE_CHART \d \d DIM_LENGTH: 0 \d+$", text, flags=re.M)) == 16,
            "d4 boundary report does not cover all 16 trace charts")
    require(len(re.findall(r"^REDUCED_CHART \d \d LENGTH_ALLROOTS: \d+ 1$", text, flags=re.M)) == 16,
            "d4 boundary reduced-chart checks are incomplete")
    require(len(re.findall(r"^REDUCED_CHART \d \d SEPARABLE: 1$", text, flags=re.M)) == 16,
            "d4 boundary reduced-chart separability check failed")
    expected = {"FULL": 768, "TRACE": 384, "REDUCED": 48}
    got = {}
    for label, total in expected.items():
        values = [int(x) for x in re.findall(rf"^{label}_CELL \d+ \d+ LENGTH: (\d+)$", text, flags=re.M)]
        require(len(values) == 16 and sum(values) == total,
                f"d4 boundary {label.lower()} cell sum is incomplete")
        got[label.lower() + "_cell_length"] = sum(values)
    return {"characteristic": characteristic, **got, "charts": 16}


def check_d4_lower(report: dict[str, Any]) -> dict[str, Any]:
    upper = report["d4_upper"]
    require(upper.get("completed") is True and upper.get("dimension") == 0
            and upper.get("quotient_dimension") == 512
            and upper.get("generator_remainders_zero") == 1,
            "d4 lower-route exact upper model report failed")
    d4 = report["d4"]
    require(d4.get("known_distinct_chart_points") == 512
            and d4.get("complete_classification") is True,
            "d4 lower report does not supply 512 certified points")
    packets = d4["packets"]
    require(set(packets) == {"physical", "ghost"}, "d4 physical/Galois mate pair is incomplete")
    for label, packet in packets.items():
        require(packet["fourier_equations"] == 16 and packet["WH_trace_products"] == 15,
                "d4 exact projector equation checks are incomplete: " + label)
        require(packet["stabilizer_order"] == 6 and packet["orbit_size"] == 256,
                "d4 exact orbit/stabilizer mismatch: " + label)
        require(packet["zero_first_ket_images"] == packet["zero_first_bra_images"] == 0,
                "d4 known orbit left its normalized chart: " + label)
    require(packets["physical"]["nonHermitian_witness"] is None
            and packets["ghost"]["nonHermitian_witness"], "d4 Galois mate distinction failed")
    require(d4.get("disjointness"), "d4 orbit disjointness argument is missing")
    return {"known_distinct_points": 512, "orbit_sizes": [256, 256],
            "physical_and_nonhermitian_mate": True}


def check_d4(root: Path, upper_stdout: str, *, fresh: bool) -> dict[str, Any]:
    upper = check_d4_fiber_output(upper_stdout)
    base = root / "sources/d4-upper/numerics"
    boundaries = [check_d4_boundary(base / f"e10_d4_p{p}.out", p) for p in (0, 5)]
    lower_path = root / "sources/d4-lower/data/e01_exact_complex_calibration.json"
    lower = check_d4_lower(_require_json(lower_path, "d4 exact lower-bound"))
    return {"open_fibre": upper, "boundary": boundaries, "lower_bound": lower,
            "historical_or_fresh": "fresh" if fresh else "historical"}


def check_d5_fibre(path: Path, d3_path: Path, d5_path: Path) -> dict[str, Any]:
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    for key, expected in (("FULL_DIM", 0), ("FULL_LENGTH", 4000), ("NULL_DIM", 0),
                          ("NULL_LENGTH", 2000), ("TRACE_SQUARE_REMAINDER", 0)):
        match = re.search(rf"^{key}\s+(-?\d+)$", text, flags=re.M)
        require(match is not None and int(match.group(1)) == expected,
                f"d5 special-fibre {key} did not equal {expected}")
    require("BEGIN_LEX" in text and "END_LEX" in text, "d5 special-fibre lex basis is missing")
    require("TIMEOUT" not in text and not re.search(r"^\s*\?", text, flags=re.M),
            "d5 special-fibre Singular process failed")
    d3 = _require_json(d3_path, "d5 finite-field solve")
    require(d3.get("d") == 5 and d3.get("p") == 3 and d3.get("q") == 6561
            and d3.get("expected_length_trace_zero_chart") == 2000
            and d3.get("distinct_chart_points") == 2000 and d3.get("complete_reduced_chart") is True,
            "d5 finite-field trace-zero chart is incomplete")
    require(len(d3.get("points", [])) == 2000 and len({json.dumps(x, separators=(",", ":"))
            for x in d3["points"]}) == 2000, "d5 trace-zero point list is not 2000 distinct points")
    d5 = _require_json(d5_path, "d5 point analysis")
    require(d5.get("d") == 5 and d5.get("p") == 3 and d5.get("q") == 6561
            and d5.get("chart_points") == 2000 and d5.get("whole_fibre_points") == 2000,
            "d5 complete-fibre point report is incomplete")
    require(len(d5.get("per_point", [])) == 2000 and len(d5.get("Frob_p_permutation", [])) == 2000,
            "d5 per-point or Frobenius report is incomplete")
    require(all(row["jacobian"].get("rank_equal") == 7 and row["jacobian"].get("rank_null") == 8
                for row in d5["per_point"]), "d5 local Jacobian ranks fail")
    return {"full_scheme_length": 4000, "trace_zero_length": 2000,
            "trace_zero_points": 2000, "local_jacobian_records": 2000}


def check_d5_support(root: Path) -> dict[str, Any]:
    support = _require_json(root / "sources/escape/numerics/e90_support_audit.json", "d5 support census")
    census = [r for r in support.get("censuses", []) if (r.get("d"), r.get("p")) == (5, 3)]
    require(len(census) == 1, "d5 p=3 support census missing or repeated")
    row = census[0]
    require(row.get("opposite_pairs") == 12 and row.get("sl2_order") == 120
            and row.get("nonempty_orbits") == 2 and row.get("nonempty_supports") == 48,
            "d5 p=3 support census has wrong totals")
    strata = [r for r in support.get("strata", []) if (r.get("d"), r.get("p")) == (5, 3)]
    require(strata and len({r["mask"] for r in strata}) == len(strata),
            "d5 p=3 support strata are incomplete or duplicated")
    require(sum(r["orbit_size"] for r in strata if r["dim"] >= 0) == 48,
            "d5 p=3 realized supports do not total 48")
    return {"support_orbits": row["nonempty_orbits"], "realizable_supports": row["nonempty_supports"],
            "enumerated_strata": len(strata)}


def check_d5_cells(path: Path) -> dict[str, Any]:
    report = _require_json(path, "d5 cell audit")
    require(report.get("d") == 5 and report.get("p") == 3
            and report.get("old_minimal_cut_identities") == 15
            and report.get("new_minimal_cut_identities") == 43
            and report.get("large_support_cut_identities") == 1
            and report.get("cut_formula_equivalence_checks") == 58,
            "d5 cell audit identity counts are incomplete")
    records = report.get("records", [])
    require(len(records) == 59, "d5 unit/cell identity report must contain 59 entries")
    require(all(r.get("identity") == "exactly 1" and r.get("cell_leaders") == "exact match"
                and r.get("replay_sha256") for r in records), "d5 stored cell identity failed")
    require(report.get("minimal_final") == "unsat" and report.get("large_final") == "unsat",
            "d5 final weighted systems were not both UNSAT")
    require(len(report.get("minimal_final_smt_files", [])) == 5
            and re.fullmatch(r"[0-9a-f]{64}", report.get("minimal_final_sha256", ""))
            and re.fullmatch(r"[0-9a-f]{64}", report.get("large_final_sha256", "")),
            "d5 final SMT input bindings are incomplete")
    return {"unit_identities": 59, "formula_equivalences": 58,
            "minimal_system": "unsat", "large_support_system": "unsat"}


def check_d5_lower(report: dict[str, Any]) -> dict[str, Any]:
    require(report.get("group_order") == 6000 and report.get("original_exact_quartic_count") == 25
            and report.get("sigma_exact_quartic_count") == 25
            and report.get("original_exact_WH_trace_product_count") == 24
            and report.get("sigma_exact_WH_trace_product_count") == 24,
            "d5 exact lower-bound arithmetic report is incomplete")
    require(report.get("distinct_complex_chart_projectors_lower_bound") == 4000,
            "d5 exact lower-bound count is not 4000")
    orbits = report.get("orbits", {})
    require(set(orbits) == {"Hermitian_SG5a", "nonHermitian_sigmaM"}, "d5 exact orbit pair is incomplete")
    herm = orbits["Hermitian_SG5a"]
    ghost = orbits["nonHermitian_sigmaM"]
    require(herm.get("chart_root_count") == ghost.get("chart_root_count") == 2000,
            "d5 exact orbit sizes are not 2000 each")
    for name, orbit in (("Hermitian_SG5a", herm), ("nonHermitian_sigmaM", ghost)):
        require(orbit.get("enumerated_projective_elements") == 6000
                and orbit.get("stabilizer_order") == 3
                and orbit.get("projector_orbit_size") == 2000
                and orbit.get("zero_right_first_coordinates") == 0
                and orbit.get("zero_left_first_coordinates") == 0,
                "d5 exact orbit/stabilizer fields fail: " + name)
    witness = report.get("nonHermitian_projector_witness", {})
    require(isinstance(witness, dict), "d5 non-Hermitian witness is malformed")
    residual = witness.get("nonzero_residual_basis", [])
    require(len(residual) == 32 and any(value != 0 for value in residual),
            "d5 Hermitian/Galois-mate distinction failed")
    require(report.get("scope", "").startswith("lower bounds"),
            "d5 lower-bound report overstates its classification scope")
    return {"exact_lower_bound": 4000, "disjoint_orbits": [2000, 2000],
            "classification_claimed_by_seed_script": False}


def check_d5(root: Path, fibre_path: Path, *, fresh: bool) -> dict[str, Any]:
    special = root / "sources/special-fibres/numerics"
    finite = check_d5_fibre(special / "e01_d5_p3.singular.out",
                            special / "e03_d5_p3_q6561.json", special / "e05_d5_p3.json")
    support = check_d5_support(root)
    cells = check_d5_cells(root / "sources/escape/numerics/e90_d5_cells_audit.json")
    lower = check_d5_lower(_require_json(root / "sources/exact-d4-d5/certificates/e09_exact_d5.json",
                                         "d5 exact lower-bound"))
    require("FULL_LENGTH 4000" in fibre_path, "fresh d5 output omitted complete-fibre length")
    return {"special_fibre": finite, "support_audit": support, "escape_audit": cells,
            "exact_lower_bound": lower, "historical_or_fresh": "fresh" if fresh else "historical"}


def check_d6(root: Path, *, fresh: bool) -> dict[str, Any]:
    path = root / "sources/d6/numerics/e43_replay_all.json"
    report = _require_json(path, "d6 replay")
    require(report.get("status") == "PASS", "d6 report did not pass")
    if fresh:
        require(report.get("records_only") is False, "d6 report is not a fresh replay")
    else:
        require(isinstance(report.get("records_only"), bool), "historical d6 mode field is missing")
    require(report.get("identity_count") == 147 and report.get("six_fresh_covers") == "UNSAT"
            and report.get("full_special_points") == 3456 and report.get("full_complex_points") == 6912,
            "d6 replay summary counts are incomplete")
    require(report.get("upper_bound_recomputed") is True,
            "d6 trace-section upper bound was not recomputed")
    stages = report.get("stages", [])
    expected = {"e40_replay_boundary.py", "e41_replay_inputs.py", "e42_replay_known_orbits.py",
                "e90_component_audit.py", "e90_r1_plain_audit.py"}
    require({r.get("script") for r in stages} == expected and len(stages) == 5,
            "d6 five-stage execution record is incomplete")
    fresh_or_old = "e43_e42_replay_known_orbits.out" if fresh else "e42_replay_known_orbits.out"
    if fresh:
        orbit_path = root / "sources/d6/numerics/e43_e42_replay_known_orbits.out"
        require(fresh_or_old in report.get("records", {}) and orbit_path.is_file()
                and report["records"][fresh_or_old] == sha256(orbit_path),
                "d6 report does not bind the fresh orbit output bytes")
        require(report.get("upper_bound_recomputed") is True,
                "d6 trace-section upper bound was not recomputed")
        selected = claim_provenance(root, "d6")
        require(len(selected) == 291,
                "d6 publication provenance does not match the complete 291-file input closure")
        boundary = _require_json(root / "sources/d6/numerics/e40_replay_boundary.json",
                                 "d6 fresh boundary replay")
        residue_flags = Counter((row.get("normalized_residue_point"), row.get("residue_component"))
                                for row in boundary.get("identities", []))
        require(boundary.get("status") == "PASS" and boundary.get("identity_count") == 147
                and boundary.get("complete_boundary_coverage") is True
                and len(boundary.get("identities", [])) == 147
                and all(row.get("identity") == "exactly 1" for row in boundary["identities"])
                and residue_flags == Counter({(True, False): 133,
                                               (False, False): 13,
                                               (False, True): 1}),
                "d6 fresh boundary identities are incomplete")
        covers = boundary.get("covers", [])
        require(len(covers) == 6 and all(row.get("status") == "unsat"
                                        and row.get("uses_e31") is False
                                        and row.get("uses_saved_smt") is False for row in covers),
                "d6 boundary replay needs six fresh UNSAT covers")
        inputs = _require_json(root / "sources/d6/numerics/e41_replay_inputs.json",
                               "d6 fresh input replay")
        stages = inputs.get("stages", {})
        require(inputs.get("status") == "PASS" and inputs.get("recomputed_trace_upper") is True
                and set(stages) == {"support", "geometry", "seed"},
                "d6 input replay stages are incomplete")
        support = stages["support"]
        support_details = _require_json(root / "sources/d6/numerics/e41_support.json",
                                        "d6 exhaustive support output")
        require(support.get("status") == "PASS" and len(support.get("nonempty", [])) == 6
                and support.get("compilation", {}).get("status") == "complete"
                and support.get("census", {}).get("status") == "complete",
                "d6 support replay is incomplete")
        require(support_details.get("status") == "PASS"
                and len(support_details.get("all_strata", [])) == 420
                and len(support_details.get("nonempty", [])) == 6,
                "d6 support replay does not cover all 420 strata")
        geometry = stages["geometry"]
        require(geometry.get("status") == "PASS" and geometry.get("points") == 3456
                and geometry.get("full_special_length") == 6912
                and geometry.get("trace_upper", {}).get("mode") == "recomputed GB"
                and geometry.get("trace_upper", {}).get("length") == 3456
                and geometry.get("group_replay", {}).get("verified") is True
                and geometry.get("group_replay", {}).get("points") == 3456
                and geometry.get("group_replay", {}).get("ordinary_orbits") == 2,
                "d6 geometry replay fields are incomplete")
        seed = stages["seed"]
        require(seed.get("status") == "PASS" and len(seed.get("root_classes", [])) == 13
                and seed.get("child", {}).get("returncode") == 0
                and seed.get("exact_seed") == "rank one, Hermitian, trace one, all signed integer-label SIC equations",
                "d6 exact Hermitian seed replay failed")
        orbit = _require_json(orbit_path, "d6 fresh known-orbit certificate")
        require(orbit.get("status") == "CERTIFIED" and orbit.get("returncode") == 0
                and orbit.get("schema") == "sic-d6-ordinary-norm-certificate-v1"
                and len(orbit.get("axis_representatives", [])) == 12
                and orbit.get("stderr") == "",
                "d6 fresh known-orbit certificate failed")
        component = _require_json(root / "sources/d6/numerics/e90_component_audit.json",
                                  "d6 component audit")
        plain = _require_json(root / "sources/d6/numerics/e90_r1_plain_audit.json",
                              "d6 plain audit")
        require(component.get("status") == "PASS" and plain.get("status") == "PASS",
                "d6 exact audit report failed")
    else:
        require(report.get("checked_dependency_hashes", 0) > 0,
                "historical d6 report has no dependency hash checks")
    return {"status": "PASS", "input_chain_files": 291, "identities": 147,
            "fresh_unsat_covers": 6, "special_points": 3456, "generic_points": 6912,
            "upper_bound_recomputed": True, "historical_or_fresh": "fresh" if fresh else "historical"}


def check_d7_finiteness(out_dir: Path, *, fresh: bool) -> dict[str, Any]:
    out_dir = Path(out_dir)
    self_report = _require_json(out_dir / "self.json", "d7 finiteness self-test")
    for key in ("tau7_is_1", "reconstruction_7abT", "c_q_equals_Z_minus_q", "minors_vanish_on_rank1",
                "squares_vanish_on_rank1", "row_witness_C", "products_zero_on_row", "z0_zero_on_row",
                "parse_ty", "parse_prod", "parse_trace_is_z0sq_minus_8t", "parse_bare_coeff", "parse_pow"):
        require(self_report.get(key) is True, "d7 finiteness self-test failed: " + key)

    n1 = _require_json(out_dir / "n1.json", "d7 finiteness coefficient valuation")
    roots = n1.get("roots", [])
    require(len(roots) == 6 and len(set(roots)) == 6 and all(pow(r, 7, 29) == 1 and r != 1 for r in roots),
            "d7 finiteness valuation report has the wrong six roots")
    coeffs = n1.get("n_minor_coefficients")
    require(coeffs == 40131 and n1.get("n_unit_at_all_six_primes") == 40131
            and n1.get("n_positive_at_some_prime") == 0,
            "d7 finiteness coefficient valuation counts are wrong")
    hist = n1.get("histogram", {})
    require(set(hist) == {str(r) for r in roots}
            and n1.get("working_tau") == 16
            and all(hist[str(r)] == {"0": 40131} for r in roots),
            "d7 finiteness valuation histograms are incomplete")

    n2 = _require_json(out_dir / "n2.json", "d7 finiteness support census")
    require(n2.get("tau") == 16
            and n2.get("group_conjugation_order") == n2.get("abstract_SL2_order") == 336
            and n2.get("group_generators_failed") == 0 and n2.get("group_generators_ok", 0) > 0
            and n2.get("conjugation_equals_some_SL2_action") is True,
            "d7 finiteness support group census failed")
    require(n2.get("base_patterns") == 343 and n2.get("closed_patterns") == 2401
            and n2.get("seed_union") == n2.get("published_union_conjugation")
            == n2.get("published_union_abstract") == n2.get("claimed_blocked") == 544
            and n2.get("n_claimed_fail") == 0 and not n2.get("claimed_fail_closed_patterns")
            and n2.get("z3_closed_outside_claimed") == "unsat",
            "d7 finiteness 544-support exclusion failed")
    expected_orbits = [(7, 48), (14, 48), (14, 48), (20, 336), (21, 16), (21, 48)]
    def orbit_pairs(rows: Any) -> list[tuple[int, int]]:
        require(isinstance(rows, list), "d7 support orbit list is malformed")
        try:
            return sorted((int(row["size"]), int(row["orbit"])) for row in rows)
        except (KeyError, TypeError, ValueError) as exc:
            raise AcceptanceError("d7 support orbit record is malformed") from exc
    require(orbit_pairs(n2.get("seed_orbit_summary")) == expected_orbits
            and orbit_pairs(n2.get("published_under_conjugation")) == expected_orbits
            and orbit_pairs(n2.get("published_under_abstract_SL2")) == expected_orbits
            and all(row.get("in_seed_covered") is True
                    for row in n2.get("published_under_conjugation", [])),
            "d7 finiteness six support orbit sizes are wrong")
    require(n2.get("explicit_masks_outside_claimed") == []
            and n2.get("claimed_fail_closed_patterns") == [],
            "d7 finiteness has explicit support masks outside the claimed set")
    ghost = n2.get("base_ghost_example")
    if ghost is not None:
        require(ghost.get("passes_base") is True and ghost.get("passes_closed") is False,
                "d7 base-pattern ghost is not excluded by the closed pattern set")

    n3 = _require_json(out_dir / "n3.json", "d7 finiteness identity audit")
    rows = n3.get("results", [])
    require(n3.get("merge_status_field") == "PASS" and n3.get("n") == len(rows) == 25,
            "d7 finiteness requires all 25 authenticated identities")
    require(all(row.get("sum_is_1") is True and row.get("step_fail") is None
                and row.get("n_dependency_missing", 0) == 0 and row.get("n_declared_extra_leaves", 0) == 0
                for row in rows),
            "one or more d7 finiteness identities failed exact replay")
    expanded = sum(row.get("schema") == "portable-unit-cell-v1" for row in rows)
    circuit_rows = [row for row in rows if row.get("schema") == "portable-unit-circuit-v1"]
    circuits = len(circuit_rows)
    require(expanded == 21 and circuits == 4, "d7 finiteness identity type counts are wrong")
    for row in rows:
        circuit = row["schema"] == "portable-unit-circuit-v1"
        # Circuit samples are historical diagnostics. Only the complete list of
        # unmatched dependency leaves measures the authentication still needed.
        key = "unmatched_used_generator_indices" if circuit else "unmatched_generator_indices"
        unmatched = row.get(key)
        require(isinstance(unmatched, list)
                and row.get("unmatched_not_explained") == []
                and row.get("unmatched_linear_in_block_span") == len(unmatched),
                "d7 finiteness has unexplained or unverified generators")
        if circuit:
            matched = row.get("used_generators_matched_to_model")
            used = row.get("n_used_leaves")
            require(isinstance(matched, int) and matched >= 0
                    and isinstance(used, int) and used >= 0
                    and len(set(unmatched)) == len(unmatched)
                    and matched + len(unmatched) == used,
                    "d7 finiteness circuit generator audit does not cover every used leaf")
    require(all(row.get("n_nonhomogeneous_truncated") == 0
                and not row.get("nonhomogeneous_generators_sample", []) for row in circuit_rows),
            "d7 finiteness circuit identities contain nonhomogeneous truncated generators")

    n4 = _require_json(out_dir / "n4.json", "d7 finiteness full weight cover")
    blocks = n4.get("blocks", [])
    require(len(blocks) == 11 and n4.get("n_patterns", 0) > 0,
            "d7 finiteness requires ten rectangles and the twenty-label type")
    rectangle = [r for r in blocks if r.get("kind") != "twenty-element-base"]
    twenty = [r for r in blocks if r.get("kind") == "twenty-element-base"]
    require(len(rectangle) == 10 and len(twenty) == 1 and twenty[0].get("mask") == 267386752,
            "d7 finiteness rectangle/type coverage is incomplete")
    require(all(str(r.get("z3", "")).lower() == "unsat" for r in blocks),
            "a d7 finiteness weight cover was not UNSAT")
    require(sum(r.get("n_certificates", 0) for r in rectangle) == 25
            and all(r.get("n_cells_used", 0) == r.get("n_certificates") > 0 for r in rectangle),
            "d7 finiteness rectangle covers do not consume every identity")
    require(all(len(r.get("notes", [])) == r.get("n_certificates")
                and all(not note.get("notes") and note.get("certificate_weight_in_cell") is True
                        and note.get("n_cell_entries") == note.get("n_cell_polys")
                        for note in r["notes"]) for r in rectangle),
            "d7 finiteness has unresolved rectangle cell mappings")
    return {"stages": ["self", "n1", "n2", "n3", "n4"], "valuation_roots": 6,
            "support_types": 6, "support_count": 544, "unit_identities": 25,
            "expanded_identities": expanded, "circuit_identities": circuits,
            "weight_covers": 11, "all_covers": "unsat",
            "historical_or_fresh": "fresh" if fresh else "historical"}


def check_d7_faces(root: Path, out: Path, *, fresh: bool) -> dict[str, Any]:
    driver = root / "replay/d7_faces.py"
    require(driver.is_file(), "missing portable d7_faces.py driver")
    spec = importlib.util.spec_from_file_location("replay_d7_faces_acceptance", driver)
    require(spec is not None and spec.loader is not None, "cannot load face acceptance module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.validate_reports(Path(out))
    return {"cones": 12, "prime_seed_runs": 48, "face_checks": "accepted",
            "higher_order_path_exhaustion_claimed": False,
            "historical_or_fresh": "fresh" if fresh else "historical"}


def _bind_report_file(directory: Path, name: str, expected: str) -> Path:
    safe = safe_relative_path(name)
    require(len(safe.parts) == 1, "count report filename must be a basename")
    path = directory / safe.name
    require(path.is_file(), "missing report bound by count file: " + safe.name)
    require(sha256(path) == expected, "count report hash binding mismatch: " + safe.name)
    return path


def _report_basename(value: Any, context: str) -> str:
    safe = safe_relative_path(str(value))
    require(len(safe.parts) == 1, context + " must be a basename")
    return safe.name


def _require_original_hash_for_basename(root: Path, basename: str, expected: str) -> None:
    by_path, _ = provenance_index(root)
    matches = [item for path, item in by_path.items() if PurePosixPath(path).name == Path(basename).name]
    require(len(matches) == 1, "historical hash source is missing or ambiguous: " + Path(basename).name)
    require(matches[0]["original_sha256"] == expected,
            "historical embedded hash differs from source-byte provenance: " + Path(basename).name)


def _rooted_recorded_path(root: Path, value: str) -> Path:
    """Resolve a report path only when it remains inside the package root."""
    root = Path(root).resolve()
    candidate = Path(value)
    if candidate.is_absolute():
        candidate = candidate.resolve()
        try:
            relative = candidate.relative_to(root)
        except ValueError as exc:
            raise AcceptanceError("report names an output outside the isolated package tree") from exc
        return root / relative
    safe = safe_relative_path(value)
    return root.joinpath(*safe.parts)


def check_d7_spurious(root: Path, *, fresh: bool,
                      fresh_count_path: str | Path | None = None) -> dict[str, Any]:
    numerics = root / "sources/d7/numerics"
    if fresh:
        count_path = Path(fresh_count_path) if fresh_count_path is not None else None
        if count_path is not None and not count_path.is_absolute():
            count_path = root / count_path
        require(count_path is not None and count_path.is_file(), "missing fresh d7 independent count report")
    else:
        count_path = numerics / "e44_d7_second_batch_v1_count.json"
        require(count_path.is_file(), "missing historical d7 independent count report")
    count = _require_json(count_path, "d7 independent count")
    require(count.get("d") == 7 and count.get("passed") is True
            and count.get("certified_orbits") == 21232 and count.get("orbit_size") == 98
            and count.get("certified_spur_lower_bound") == 2080736,
            "d7 independent count report failed")
    for key in ("root_exist_unique", "jacobian_nonsingular", "all_off_base",
                "complete_nonidentity_freeness_checks", "all_orbit_pairs_distinct"):
        require(count.get(key) is True, "d7 independent count missing acceptance: " + key)
    require(count.get("integer_interval_bits") == 384 and count.get("meets_d7_full_target") is True
            and count.get("exceeds_d7_budget") is False and count.get("conditional_upper_after_cone_bound") == 32928,
            "d7 independent count budget fields are wrong")
    snapshot_path = numerics / _report_basename(count.get("root_snapshot_file"),
                                                "d7 root snapshot filename")
    snap_info = check_frozen_snapshot(snapshot_path, require_frozen_hash=True)
    if fresh:
        require(count.get("root_snapshot_sha256") == sha256(snapshot_path),
                "fresh count does not bind its root snapshot")
    else:
        require(count.get("root_snapshot_sha256") == FROZEN_SNAPSHOT_SHA256,
                "historical count references the wrong frozen snapshot")
    header_path = numerics / _report_basename(count.get("header_file"), "d7 header filename")
    require(sha256(header_path) == count["header_sha256"] == snap_info["header_sha256"],
            "d7 count/header binding mismatch")
    matrix_path = numerics / "e40_d7_matrix.json"
    require(sha256(matrix_path) == count["exact_matrix_sha256"] == snap_info["matrix_sha256"],
            "d7 count/matrix binding mismatch")
    root_result_path = numerics / _report_basename(count.get("root_checker_result"),
                                                    "d7 root-result filename")
    sep_manifest_path = numerics / _report_basename(count.get("separation_manifest"),
                                                     "d7 separation-manifest filename")
    sep_result_path = numerics / _report_basename(count.get("separation_checker_result"),
                                                   "d7 separation-result filename")
    if fresh:
        for name, key in ((count["root_checker_result"], "root_checker_result_sha256"),
                          (count["separation_manifest"], "separation_manifest_sha256"),
                          (count["separation_checker_result"], "separation_checker_result_sha256")):
            _bind_report_file(numerics, name, count[key])
    else:
        for key in ("root_checker_result", "separation_manifest", "separation_checker_result",
                    "root_snapshot_file", "header_file"):
            _require_original_hash_for_basename(root, count[key], count[
                {"root_checker_result": "root_checker_result_sha256",
                 "separation_manifest": "separation_manifest_sha256",
                 "separation_checker_result": "separation_checker_result_sha256",
                 "root_snapshot_file": "root_snapshot_sha256",
                 "header_file": "header_sha256"}[key]])
        _require_original_hash_for_basename(root, "e40_d7_matrix.json", count["exact_matrix_sha256"])
        _require_original_hash_for_basename(root, "e43_d7_q_basis.json", count["q_basis_sha256"])
        require(root_result_path.is_file() and sep_manifest_path.is_file() and sep_result_path.is_file(),
                "historical d7 root/separation report originals are missing")
    roots = _require_json(root_result_path, "d7 root checker")
    separation = _require_json(sep_result_path, "d7 independent separation checker")
    sep_manifest = _require_json(sep_manifest_path, "d7 separation manifest")
    require(roots.get("passed") is True and roots.get("checked_representatives") == 21232
            and roots.get("freeness_checks") == 21232 * 97,
            "d7 interval root checks are incomplete")
    require(separation.get("passed") is True and separation.get("all_pairwise_separation") is True
            and separation.get("checked_representatives") == 21232,
            "d7 independent interval separation failed")
    snapshot = load_json(snapshot_path)
    ids = [ident for chunk in snapshot["chunks"] for ident in chunk["ids"]]
    ids_sha = hashlib.sha256(json.dumps(sorted(ids), separators=(",", ":")).encode()).hexdigest()
    require(roots.get("representative_ids_sha256") == separation.get("representative_ids_sha256")
            == count.get("representative_ids_sha256") == ids_sha,
            "d7 interval reports do not bind the complete representative ID set")
    require(roots.get("header_sha256") == separation.get("header_sha256") == count["header_sha256"],
            "d7 interval header binding mismatch")
    expected_chunks = {row["file"]: row["sha256"] for row in snapshot["chunks"]}
    def normalized(mapping: Any) -> dict[str, Any]:
        require(isinstance(mapping, dict), "certificate hash mapping missing")
        out = {Path(k).name: v for k, v in mapping.items()}
        require(len(out) == len(mapping), "ambiguous repeated certificate basenames")
        return out
    require(normalized(roots.get("certificate_sha256")) == expected_chunks
            and normalized(separation.get("certificate_sha256")) == expected_chunks,
            "d7 reports do not bind the exact 886 root chunks")
    require(roots.get("matrix_binding", {}).get("sha256")
            == separation.get("matrix_binding", {}).get("sha256") == count["exact_matrix_sha256"],
            "d7 root and separation reports disagree on the matrix")
    require(roots.get("checker_sha256") == separation.get("checker_sha256"),
            "d7 independent checker source binding differs")
    root_matrix = roots.get("matrix_binding", {})
    sep_matrix = separation.get("matrix_binding", {})
    require(root_matrix.get("exact_entries_verified") is True
            and sep_matrix.get("exact_entries_verified") is True,
            "d7 root/separation reports did not verify every exact matrix entry")
    published_checker = root / "sources/d7/numerics/e42_spur_independent.py"
    require(published_checker.is_file(), "published d7 independent checker source is missing")
    checker_hash = sha256(published_checker)
    checker_item = provenance_index(root)[0].get("sources/d7/numerics/e42_spur_independent.py")
    require(checker_item is not None and checker_item["sha256"] == checker_hash,
            "published d7 independent checker is not bound by provenance")
    if fresh:
        recorded_checker = _rooted_recorded_path(root, count["checker_source_file"])
        require(recorded_checker.is_file() and sha256(recorded_checker) == checker_hash
                and count.get("checker_source_sha256") == checker_hash
                and roots.get("checker_sha256") == separation.get("checker_sha256") == checker_hash,
                "fresh d7 reports do not bind the published e42 checker bytes")
        require(separation.get("manifest_sha256") == sha256(sep_manifest_path)
                == count.get("separation_manifest_sha256"),
                "fresh d7 separation result does not bind its manifest bytes")
    else:
        _require_original_hash_for_basename(root, "e42_spur_independent.py",
                                            count["checker_source_sha256"])
        require(roots.get("checker_sha256") == separation.get("checker_sha256")
                == count.get("checker_source_sha256"),
                "historical d7 reports disagree on the original checker bytes")
        require(separation.get("manifest_sha256") == count.get("separation_manifest_sha256"),
                "historical separation report does not bind its recorded manifest")
    require(sep_manifest.get("individual_manifest_sha256") == count.get("root_snapshot_sha256"),
            "d7 separation manifest does not bind the frozen root snapshot")
    require(sep_manifest.get("basis_sha256") == count.get("q_basis_sha256"),
            "d7 separation manifest q-basis binding mismatch")

    if fresh:
        basis_replay = _require_json(numerics / "e43_d7_q_basis_replay.json", "d7 q-basis replay")
        require(basis_replay.get("passed") is True and basis_replay.get("rank") == 15
                and basis_replay.get("coefficient_identities_checked") == 2688,
                "fresh d7 q-basis check failed")
        symmetry = _require_json(numerics / "e45_d7_symmetry.json", "d7 symmetry replay")
        require(symmetry.get("status") == "PASS" and symmetry.get("d") == 7
                and symmetry.get("q_equations") == 24 and symmetry.get("group_order") == 98
                and symmetry.get("all_projective_normal_forms_distinct") is True
                and symmetry.get("multiplication_pairs_checked") == 98 * 98,
                "fresh d7 exact symmetry check failed")
        independent = _require_json(root / "independent/d7-spurious/out/summary.json",
                                    "d7 independent full-root report")
    else:
        independent = _require_json(root / "independent/d7-spurious/out/summary.json",
                                    "d7 historical independent full-root report")
    for key in ("n_records", "n_ok", "unique_ids", "n_scheduled"):
        require(independent.get(key) == 21232, "d7 independent full-root count mismatch: " + key)
    for key in ("n_bad", "stab_failures", "q_failures", "real_clusters_gt1", "n_unseparated_pairs"):
        require(independent.get(key) == 0, "d7 independent full-root failure: " + key)
    require(independent.get("largest_real_cluster") == 1 and not independent.get("bad_ids")
            and not independent.get("bad_stages") and not independent.get("unseparated_pairs"),
            "d7 independent interval report has unresolved roots")
    if fresh:
        require(roots.get("representative_ids_sha256") == count["representative_ids_sha256"],
                "fresh root report ID hash differs from count")
    return {"count_report": count_path.name, "certified_orbits": 21232, "orbit_size": 98,
            "off_base_lower_bound": 2080736, "snapshot": snap_info,
            "root_checker": "accepted", "independent_separation": "accepted",
            "independent_full_root_records": 21232,
            "historical_or_fresh": "fresh" if fresh else "historical"}


def check_ghosts(root: Path) -> dict[str, Any]:
    """Check inherited classifications and displaced-parity branch arithmetic.

    This accepts reports and arithmetic used by the written proof. It does not
    prove the paper lemmas or rerun any point classification.
    """
    d4 = _require_json(root / "sources/d4-lower/data/e01_exact_complex_calibration.json",
                       "d4 Galois mate record")
    d4_summary = check_d4_lower(d4)
    d5 = _require_json(root / "sources/exact-d4-d5/certificates/e09_exact_d5.json",
                       "d5 Galois mate record")
    d5_summary = check_d5_lower(d5)
    d6 = check_d6(root, fresh=False)
    d7_report = _require_json(root / "independent/d7-orbits/summary.json", "d7 exact orbit report")
    d7 = check_d7_orbits(d7_report)
    exact_seeds = d7_report["exact"]["seeds"]
    require(exact_seeds["F1"].get("hermitian") is True
            and exact_seeds["F2"].get("hermitian") is True
            and exact_seeds["G1"].get("hermitian") is False
            and exact_seeds["G2"].get("hermitian") is False,
            "d7 exact physical/non-Hermitian seed labels failed")

    dimensions = (4, 5, 6, 7)
    total_points = {4: 512, 5: 4000, 6: 6912, 7: 32928}
    hermitian_points = {4: 256, 5: 2000, 6: 3456, 7: 16464}
    centers = {4: 4, 5: 25, 6: 9, 7: 49}
    branch_sizes = {4: 64, 5: 80, 6: 384, 7: 336}
    parity_matrix_counts = {d: (7 * d * d // 4 if d % 2 == 0 else d * d) for d in dimensions}
    actual_branch_counts = {d: (d * d // 4 if d % 2 == 0 else d * d) for d in dimensions}
    require(all(actual_branch_counts[d] * branch_sizes[d] == hermitian_points[d]
                and total_points[d] == 2 * hermitian_points[d] for d in dimensions),
            "displaced-parity branch/ghost count arithmetic failed")
    require(d4["d4"]["known_distinct_chart_points"] == total_points[4]
            and d5["distinct_complex_chart_projectors_lower_bound"] == total_points[5]
            and d6["special_points"] == hermitian_points[6]
            and d6["generic_points"] == total_points[6]
            and sum(row["size"] for row in d7_report["primes"]["673"]["ordinary_orbits"])
            == total_points[7],
            "inherited dimension-by-dimension point totals disagree with branch arithmetic")
    classification = {
        "d4": {"all_points": total_points[4], "hermitian": hermitian_points[4],
               "nonhermitian": hermitian_points[4], "exact_orbit_records": 2},
        "d5": {"recorded_distinct_lower_bound": d5_summary["exact_lower_bound"],
               "hermitian_seed_orbit": 2000, "nonhermitian_seed_orbit": 2000,
               "seed_script_claims_complete_classification": False},
        "d6": {"replayed_full_points": d6["generic_points"],
               "replayed_special_points": d6["special_points"],
               "known_special_ordinary_orbits": 2},
        "d7": {"ordinary_orbits": 6, "ordinary_orbit_size": 5488,
               "extended_families": 4, "nonhermitian_seeds": ["G1", "G2"]},
    }
    branch_arithmetic = {
        str(d): {"distinct_actual_parity_matrices": parity_matrix_counts[d],
                 "nonempty_centers": centers[d], "nonempty_branches": actual_branch_counts[d],
                 "points_per_branch": branch_sizes[d],
                 "nonhermitian_branch_total": actual_branch_counts[d] * branch_sizes[d]}
        for d in dimensions
    }
    return {
        "inherited_classification_records": classification,
        "displaced_parity_branch_arithmetic": branch_arithmetic,
        "paper_proof_prerequisites": [
            "S_d intersect G_d is empty in dimensions 4 through 7",
            "trace-zero parity branches are empty for even dimensions",
            "Clifford and transpose transport cover every nonempty parity branch",
            "the characteristic-zero orbit classifications and reducedness are inherited evidence",
            "d7 seed parity-Hermitian identities are supplied by the written field calculations",
        ],
        "new_mathematical_computation": False,
    }


def validate_historical_claim(root: Path, claim: str) -> dict[str, Any]:
    """Accept available historical evidence without calling it a new replay."""
    if claim == "integrity":
        integrity = verify_provenance(root, claim="integrity")
        snapshot = root / "sources/d7/numerics/e44_d7_second_batch_v1_root_snapshot.json"
        snap = check_frozen_snapshot(snapshot) if snapshot.is_file() else None
        return {"integrity": integrity, "frozen_snapshot": snap,
                "new_mathematical_computation": False}
    if claim == "ghosts":
        return check_ghosts(root)
    if claim == "d4":
        out_path = root / "sources/d4-upper/numerics/e01_d4_fiber.out"
        require(out_path.is_file(), "historical d4 open-fibre transcript is missing")
        lower = _require_json(root / "sources/d4-lower/data/e01_exact_complex_calibration.json",
                              "d4 lower-bound")
        upper = lower.get("d4_upper", {})
        require(upper.get("quotient_dimension") == 512 and upper.get("completed") is True,
                "historical d4 upper report is incomplete")
        text = out_path.read_text(encoding="utf-8", errors="replace")
        check_d4_fiber_output(text)
        base = root / "sources/d4-upper/numerics"
        boundaries = [check_d4_boundary(base / f"e10_d4_p{p}.out", p) for p in (0, 5)]
        return {"historical_outputs": ["d4 open fibre", "d4 p=0 boundary", "d4 p=5 boundary"],
                "boundary": boundaries, "lower_bound": check_d4_lower(lower),
                "new_mathematical_computation": False}
    if claim == "d5":
        spec = root / "sources/special-fibres/numerics"
        finite = check_d5_fibre(spec / "e01_d5_p3.singular.out", spec / "e03_d5_p3_q6561.json",
                                spec / "e05_d5_p3.json")
        support = check_d5_support(root)
        cells = check_d5_cells(root / "sources/escape/numerics/e90_d5_cells_audit.json")
        lower = check_d5_lower(_require_json(root / "sources/exact-d4-d5/certificates/e09_exact_d5.json",
                                             "d5 exact lower-bound"))
        return {"special_fibre": finite, "support_audit": support, "escape_audit": cells,
                "exact_lower_bound": lower, "new_mathematical_computation": False}
    if claim == "d6":
        return check_d6(root, fresh=False)
    if claim == "d7-finiteness":
        return check_d7_finiteness(root / "work/d7-finiteness", fresh=False)
    if claim == "d7-faces":
        out = root / "independent/d7-faces/out"
        return check_d7_faces(root, out, fresh=False)
    if claim == "d7-spurious":
        return check_d7_spurious(root, fresh=False)
    if claim == "d7-orbits":
        report = _require_json(root / "independent/d7-orbits/summary.json", "d7 orbit")
        result = check_d7_orbits(report)
        result["new_mathematical_computation"] = False
        return result
    raise AcceptanceError("unsupported claim: " + claim)

