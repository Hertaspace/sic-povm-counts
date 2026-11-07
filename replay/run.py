#!/usr/bin/env python3
"""Run or inspect the evidence-package replay for one mathematical claim.

Usage: ``python -B replay/run.py <claim>``. Actual replay is the default for
mathematical claims. ``integrity`` and ``ghosts`` are record checks only;
``--records-only`` explicitly selects historical report validation for any
claim. Every invocation copies the repository tree to a unique work directory
and runs child processes from that disposable copy. It leaves the input tree
untouched and records the complete starting hashes and fresh output hashes in
``result.json``.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
import uuid
from typing import Any, Sequence

import checks


CLAIMS = (
    "d4", "d5", "d6", "d7-finiteness", "d7-faces", "d7-spurious",
    "d7-orbits", "ghosts", "integrity",
)
RECORD_ONLY_CLAIMS = {"ghosts", "integrity"}
DEFAULT_ROOT = Path(__file__).resolve().parents[1]


def canonical_hash(value: Any) -> str:
    raw = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def now_utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def ignore_copy(_directory: str, names: list[str]) -> set[str]:
    excluded = {".git", ".venv", "work", "__pycache__", ".pytest_cache", ".mypy_cache",
                ".ruff_cache", ".DS_Store"}
    return {name for name in names if name in excluded or name.endswith((".pyc", ".pyo"))}


def relative_inventory(rows: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    return [{"path": path, **rows[path]} for path in sorted(rows)]


def output_delta(before: dict[str, dict[str, Any]], after: dict[str, dict[str, Any]]) -> dict[str, Any]:
    changed = []
    created = []
    deleted = []
    for path in sorted(set(before) | set(after)):
        if path not in before:
            created.append({"path": path, **after[path]})
        elif path not in after:
            deleted.append({"path": path, **before[path]})
        elif before[path] != after[path]:
            changed.append({"path": path, "before": before[path], "after": after[path]})
    return {"created": created, "changed": changed, "deleted": deleted}


class ReplaySession:
    def __init__(self, root: Path, run_dir: Path, timeout: int, threads: int):
        self.root = root.resolve()
        self.run_dir = run_dir.resolve()
        self.workspace = self.run_dir / "repo"
        self.logs = self.run_dir / "logs"
        self.timeout = timeout
        self.threads = threads
        self.commands: list[dict[str, Any]] = []
        self.cleared_outputs: list[dict[str, Any]] = []

    def create(self) -> None:
        self.run_dir.mkdir(parents=True, exist_ok=False)
        self.logs.mkdir(parents=True)
        # inventory_tree refuses symlinks in the included input tree; preserve
        # any ignored entries as links rather than following them during copy.
        checks.inventory_tree(self.root)
        shutil.copytree(self.root, self.workspace, ignore=ignore_copy, symlinks=True)

    def child(self, name: str, argv: Sequence[str], *, timeout: int | None = None,
              cwd: str = ".", python: bool = True) -> str:
        requested_timeout = self.timeout if timeout is None else timeout
        timeout = min(requested_timeout, self.timeout)
        actual = [sys.executable, "-B", *argv] if python else list(argv)
        child_cwd = self.workspace if cwd == "." else self.workspace / cwd
        child_cwd.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env.pop("PYTHONOPTIMIZE", None)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONUNBUFFERED"] = "1"
        display = (["python3", "-B", *argv] if python else
                   ([Path(actual[0]).name, *actual[1:]] if actual else []))
        started = time.monotonic()
        proc = subprocess.Popen(
                actual,
                cwd=child_cwd,
                env=env,
                text=True,
                encoding="utf-8",
                errors="replace",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )

        def signal_group(sig: int) -> None:
            try:
                os.killpg(proc.pid, sig)
            except ProcessLookupError:
                pass

        try:
            try:
                stdout, stderr = proc.communicate(timeout=timeout)
                timed_out = False
            except subprocess.TimeoutExpired:
                timed_out = True
                signal_group(signal.SIGTERM)
                try:
                    stdout, stderr = proc.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    signal_group(signal.SIGKILL)
                    stdout, stderr = proc.communicate()
        except BaseException:
            # Also clean the owned process group if the runner is interrupted.
            signal_group(signal.SIGTERM)
            try:
                stdout, stderr = proc.communicate(timeout=2)
            except subprocess.TimeoutExpired:
                signal_group(signal.SIGKILL)
                proc.communicate()
            raise
        returncode = proc.returncode
        log_path = self.logs / (name.replace("/", "_") + ".log")
        combined = stdout + ("\n" if stdout and stderr else "") + stderr
        log_path.write_text(combined, encoding="utf-8")
        record = {
            "name": name,
            "argv": display,
            "cwd": cwd,
            "returncode": returncode,
            "timed_out": timed_out,
            "timeout_seconds": timeout,
            "seconds": round(time.monotonic() - started, 6),
            "stdout_sha256": hashlib.sha256(stdout.encode("utf-8")).hexdigest(),
            "stderr_sha256": hashlib.sha256(stderr.encode("utf-8")).hexdigest(),
            "log_path": log_path.relative_to(self.run_dir).as_posix(),
            "log_sha256": checks.sha256(log_path),
        }
        self.commands.append(record)
        checks.require(not timed_out, f"child process timed out: {name}")
        checks.require(returncode == 0, f"child process failed ({returncode}): {name}")
        return stdout

    def python(self, name: str, script: str, *args: str, timeout: int | None = None,
               cwd: str = ".") -> str:
        return self.child(name, [script, *args], timeout=timeout, cwd=cwd, python=True)

    def executable(self, name: str, *args: str, timeout: int | None = None,
                   cwd: str = ".") -> str:
        executable = shutil.which(name)
        checks.require(executable is not None, f"required executable is not on PATH: {name}")
        return self.child(name, [executable, *args], timeout=timeout, cwd=cwd, python=False)

    def clear_stale_outputs(self, patterns: Sequence[str]) -> None:
        """Remove declared prior result files from this disposable copy.

        Their starting bytes remain bound in ``source_inputs`` and the real
        package tree is never touched. Actual runs fail if any declared target
        survives this step.
        """
        for pattern in patterns:
            candidate = Path(pattern)
            checks.require(not candidate.is_absolute() and ".." not in candidate.parts,
                           "unsafe output pattern")
            for path in sorted(self.workspace.glob(pattern)):
                rel = path.relative_to(self.workspace).as_posix()
                row = {"path": rel, "sha256": checks.sha256(path) if path.is_file() else None,
                       "bytes": path.stat().st_size if path.is_file() else None}
                if path.is_dir() and not path.is_symlink():
                    shutil.rmtree(path)
                else:
                    path.unlink()
                self.cleared_outputs.append(row)
            checks.require(not list(self.workspace.glob(pattern)),
                           "stale result remained before execution: " + pattern)


def run_d4(session: ReplaySession) -> tuple[dict[str, Any], list[str]]:
    upper_stdout = session.python(
        "d4-open-fibre",
        "sources/d4-upper/numerics/e01_d4_fiber.py",
        "--complements", "--timeout", str(min(180, session.timeout)), timeout=240,
    )
    for characteristic in (0, 5):
        session.python(
            f"d4-boundary-p{characteristic}",
            "sources/d4-upper/numerics/e10_boundary.py",
            "--dimension", "4", "--characteristic", str(characteristic),
            "--all-charts", "--cells", "--timeout", str(min(30, session.timeout)), timeout=120,
        )
    session.python("d4-exact-lower-bound", "sources/d4-lower/numerics/e01_exact_complex_calibration.py",
                   timeout=600)
    acceptance = checks.check_d4(session.workspace, upper_stdout, fresh=True)
    outputs = [
        "sources/d4-upper/numerics/e01_d4_fiber.sing",
        "sources/d4-upper/numerics/e10_d4_p0.sing",
        "sources/d4-upper/numerics/e10_d4_p0.out",
        "sources/d4-upper/numerics/e10_d4_p5.sing",
        "sources/d4-upper/numerics/e10_d4_p5.out",
        "sources/d4-lower/data/e01_exact_complex_calibration.json",
    ]
    return acceptance, outputs


def run_d5(session: ReplaySession) -> tuple[dict[str, Any], list[str]]:
    session.python("d5-open-fibre", "sources/special-fibres/numerics/e01_fibre.py",
                   "5", "3", str(min(600, session.timeout)), "1", timeout=900)
    session.python("d5-trace-zero-fibre", "sources/special-fibres/numerics/e04_reduced_fibre.py",
                   "5", "3", str(min(600, session.timeout)), timeout=900)
    session.python("d5-finite-field-points", "sources/special-fibres/numerics/e03_solve.py",
                   "5", "3", "2,0,1,0,0,0,0,0,1", "e04", timeout=900)
    session.python("d5-point-analysis", "sources/special-fibres/numerics/e05_analyze.py",
                   "sources/special-fibres/numerics/e03_d5_p3_q6561.json", timeout=900)
    session.python("d5-support-audit", "sources/escape/numerics/e90_support_audit.py", timeout=1800)
    session.python("d5-cell-audit", "sources/escape/numerics/e90_d5_cells_audit.py", timeout=900)
    session.python("d5-exact-lower-bound", "sources/exact-d4-d5/numerics/e09_exact_d5.py", timeout=900)
    fibre_log = (session.logs / "d5-open-fibre.log").read_text(encoding="utf-8", errors="replace")
    acceptance = checks.check_d5(session.workspace, fibre_log, fresh=True)
    outputs = [
        "sources/special-fibres/numerics/e01_d5_p3.sing",
        "sources/special-fibres/numerics/e01_d5_p3.singular.out",
        "sources/special-fibres/numerics/e04_d5_p3.sing",
        "sources/special-fibres/numerics/e04_d5_p3.singular.out",
        "sources/special-fibres/numerics/e03_d5_p3_q6561.json",
        "sources/special-fibres/numerics/e05_d5_p3.json",
        "sources/escape/numerics/e90_support_audit.json",
        "sources/escape/numerics/e90_d5_cells_audit.json",
        "sources/exact-d4-d5/certificates/e09_exact_d5.json",
    ]
    return acceptance, outputs


def run_d6(session: ReplaySession) -> tuple[dict[str, Any], list[str]]:
    session.python("d6-full-replay", "sources/d6/numerics/e43_replay_all.py",
                   "--recompute-upper", timeout=2400)
    acceptance = checks.check_d6(session.workspace, fresh=True)
    selected = [
        "sources/d6/numerics/e43_replay_all.json",
        "sources/d6/numerics/e40_replay_boundary.json",
        "sources/d6/numerics/e41_replay_inputs.json",
        "sources/d6/numerics/e43_e42_replay_known_orbits.out",
        "sources/d6/numerics/e90_component_audit.json",
        "sources/d6/numerics/e90_r1_plain_audit.json",
    ]
    return acceptance, selected


def run_d7_finiteness(session: ReplaySession, threads: int) -> tuple[dict[str, Any], list[str]]:
    out = "work/d7-finiteness"
    session.python(
        "d7-finiteness-all-stages",
        "independent/d7-finiteness/kill_nf5.py",
        "--stage", "all", "--data", "sources/d7-finiteness/numerics", "--out", out,
        # One weight cover needed about 210 s historically and the support census about 1700 s,
        # so each solver query gets up to an hour and the whole stage the session timeout.
        "--threads", str(threads), "--timeout-ms", str(min(3600000, session.timeout * 1000)),
    )
    acceptance = checks.check_d7_finiteness(session.workspace / out, fresh=True)
    return acceptance, [f"{out}/{name}.json" for name in ("self", "n1", "n2", "n3", "n4")]


def run_d7_faces(session: ReplaySession, threads: int) -> tuple[dict[str, Any], list[str]]:
    work = "work/d7-faces-work"
    out = "work/d7-faces-out"
    (session.workspace / "work").mkdir(parents=True, exist_ok=True)
    checker = session.workspace / "independent/d7-faces/k1_face.py"
    checker_sha = checks.sha256(checker)
    session.python(
        "d7-faces-48-runs",
        "replay/d7_faces.py", "--run", "--checker", "independent/d7-faces/k1_face.py",
        "--checker-sha256", checker_sha, "--work", work, "--out", out,
        "--threads", str(threads), "--mem-gb", "20",
        "--timeout", str(min(20000, session.timeout * 1000)),
        timeout=7200,
    )
    acceptance = checks.check_d7_faces(session.workspace, session.workspace / out, fresh=True)
    produced = [p.relative_to(session.workspace).as_posix()
                for p in (session.workspace / out).glob("*") if p.is_file()]
    return acceptance, sorted(produced)


def run_d7_spurious(session: ReplaySession, threads: int, tag: str) -> tuple[dict[str, Any], list[str]]:
    numerics = "sources/d7/numerics"
    session.python(
        "d7-q-basis-replay", f"{numerics}/e43_spur_q_basis.py", "--verify",
        f"{numerics}/e43_d7_q_basis.json", "--output", f"{numerics}/e43_d7_q_basis_replay.json",
        timeout=900,
    )
    session.python("d7-exact-symmetry", f"{numerics}/e45_spur_symmetry.py", "--d", "7", timeout=900)
    session.python(
        "d7-frozen-root-replay", f"{numerics}/e44_spur_snapshot_replay.py",
        "--d", "7", "--manifest", f"{numerics}/e44_d7_second_batch_v1_root_snapshot.json",
        "--tag", tag, "--workers", str(threads), "--bits", "384", timeout=7200,
    )
    session.python("d7-independent-full-root-audit", "independent/d7-spurious/s1_cert.py",
                   "--workers", str(threads), timeout=7200)
    count = f"{numerics}/e44_d7_{tag}_count.json"
    acceptance = checks.check_d7_spurious(session.workspace, fresh=True, fresh_count_path=count)
    outdir = session.workspace / numerics
    reports = [count]
    new_prefix = f"e44_d7_{tag}_"
    reports.extend(p.relative_to(session.workspace).as_posix()
                   for p in outdir.glob(new_prefix + "*") if p.is_file())
    reports.extend(["sources/d7/numerics/e43_d7_q_basis_replay.json",
                    "sources/d7/numerics/e45_d7_symmetry.json",
                    "independent/d7-spurious/out/summary.json"])
    return acceptance, sorted(set(reports))


def run_d7_orbits(session: ReplaySession) -> tuple[dict[str, Any], list[str]]:
    tower = session.executable("gp", "-fq", "replay/check_tower.gp", timeout=180)
    checks.require("TOWER_DEGREES=[4,8,48]" in tower and "TOWER_IRREDUCIBLE=1" in tower,
                   "PARI tower irreducibility report failed")
    checks.require(not any(token in tower for token in ("? ", "***")), "PARI reported an error")
    session.python("d7-exact-orbit-audit", "../../independent/d7-orbits/audit.py",
                   timeout=1800, cwd="work/d7-orbits")
    report_path = session.workspace / "work/d7-orbits/summary.json"
    report = checks._require_json(report_path, "fresh d7 orbit")
    acceptance = checks.check_d7_orbits(report)
    acceptance["tower_irreducibility"] = "accepted"
    return acceptance, ["work/d7-orbits/summary.json"]


def execute_claim(session: ReplaySession, claim: str, threads: int, run_tag: str) -> tuple[dict[str, Any], list[str]]:
    if claim == "d4":
        return run_d4(session)
    if claim == "d5":
        return run_d5(session)
    if claim == "d6":
        return run_d6(session)
    if claim == "d7-finiteness":
        return run_d7_finiteness(session, threads)
    if claim == "d7-faces":
        return run_d7_faces(session, threads)
    if claim == "d7-spurious":
        return run_d7_spurious(session, threads, run_tag)
    if claim == "d7-orbits":
        return run_d7_orbits(session)
    raise checks.AcceptanceError(f"claim has no execution route: {claim}")


def output_patterns(claim: str, run_tag: str) -> list[str]:
    if claim == "d4":
        return [
            "sources/d4-upper/numerics/e01_d4_fiber.sing",
            "sources/d4-upper/numerics/e01_d4_fiber.out",
            "sources/d4-upper/numerics/e10_d4_p0.sing",
            "sources/d4-upper/numerics/e10_d4_p0.out",
            "sources/d4-upper/numerics/e10_d4_p5.sing",
            "sources/d4-upper/numerics/e10_d4_p5.out",
            "sources/d4-upper/numerics/e10_boundary.out",
            "sources/d4-lower/data/e01_exact_complex_calibration.json",
            "sources/d4-lower/numerics/e01_d4_trace_one.sing",
            "sources/d4-lower/numerics/e01_d4_trace_one.singular.out",
            "sources/d4-lower/offline/d5_trace_one.sing",
            "sources/d4-lower/offline/d5_zero_ket.sing",
        ]
    if claim == "d5":
        return [
            "sources/special-fibres/numerics/e01_d5_p3.sing",
            "sources/special-fibres/numerics/e01_d5_p3.singular.out",
            "sources/special-fibres/numerics/e04_d5_p3.sing",
            "sources/special-fibres/numerics/e04_d5_p3.pid",
            "sources/special-fibres/numerics/e04_d5_p3.singular.out",
            "sources/special-fibres/numerics/e03_d5_p3_q6561.json",
            "sources/special-fibres/numerics/e05_d5_p3.json",
            "sources/escape/numerics/e90_support_audit.json",
            "sources/escape/numerics/e90_support_audit.out",
            "sources/escape/numerics/e90_support_audit.bin",
            "sources/escape/numerics/e90_support_d*_p*.txt",
            "sources/escape/numerics/e90_census_d*_p*.out",
            "sources/escape/numerics/e90_stratum_last.sing",
            "sources/escape/numerics/e90_d5_cut_equivalence.out",
            "sources/escape/numerics/e90_d5_final_smt.out",
            "sources/escape/numerics/e90_d5_large_final_smt.out",
            "sources/escape/numerics/e90_d5_cells_audit.json",
            "sources/escape/numerics/e90_d5_cells_audit.out",
            "sources/exact-d4-d5/certificates/e09_exact_d5.json",
        ]
    if claim == "d6":
        return [
            "sources/d6/numerics/e43_replay_all.json",
            "sources/d6/numerics/e40_replay_boundary.json",
            "sources/d6/numerics/e41_replay_inputs.json",
            "sources/d6/numerics/e43_*.out",
            "sources/d6/numerics/e41_*.out",
            "sources/d6/numerics/e41_*.json",
            "sources/d6/numerics/e41_*.txt",
            "sources/d6/numerics/e41_*.bin",
            "sources/d6/numerics/e41_*.sing",
            "sources/d6/numerics/e90_component_audit.json",
            "sources/d6/numerics/e90_r1_plain_audit.json",
        ]
    if claim == "d7-faces":
        return ["work/d7-faces-work", "work/d7-faces-out"]
    if claim == "d7-spurious":
        return [
            "sources/d7/numerics/e43_d7_q_basis_replay.json",
            "sources/d7/numerics/e45_d7_symmetry.json",
            "independent/d7-spurious/out/summary.json",
            "independent/d7-spurious/out/part-*.json",
            "independent/d7-spurious/out/bench.json",
            f"sources/d7/numerics/e44_d7_{run_tag}_*",
            f"sources/d7/data/e44_d7_{run_tag}_*",
        ]
    if claim in {"d7-finiteness", "d7-orbits"}:
        return ["work/d7-finiteness", "work/d7-orbits"]
    return []


def declared_output_files(workspace: Path, patterns: Sequence[str]) -> list[dict[str, Any]]:
    """Return hashes for every freshly populated declared output target."""
    found: dict[str, Path] = {}
    for pattern in patterns:
        for path in workspace.glob(pattern):
            if path.is_file():
                found[path.relative_to(workspace).as_posix()] = path
            elif path.is_dir():
                for child in path.rglob("*"):
                    checks.require(not child.is_symlink(),
                                   "symlink appeared under a declared output: "
                                   + child.relative_to(workspace).as_posix())
                    if child.is_file():
                        found[child.relative_to(workspace).as_posix()] = child
    return [{"path": rel, "sha256": checks.sha256(path), "bytes": path.stat().st_size}
            for rel, path in sorted(found.items())]


def validate_write_scope(before: dict[str, dict[str, Any]], after: dict[str, dict[str, Any]],
                         patterns: Sequence[str]) -> None:
    """Reject any overwrite/removal of a pre-existing input outside outputs."""
    delta = output_delta(before, after)
    import fnmatch
    def permitted(path: str) -> bool:
        for pattern in patterns:
            if fnmatch.fnmatchcase(path, pattern):
                return True
            if not any(char in pattern for char in "*?[") and path.startswith(pattern.rstrip("/") + "/"):
                return True
        return False

    for row in delta["changed"]:
        path = row["path"]
        checks.require(permitted(path), "replay overwrote an undeclared input: " + path)
    for row in delta["deleted"]:
        path = row["path"]
        checks.require(permitted(path), "replay deleted an undeclared input: " + path)


def write_result(path: Path, result: dict[str, Any]) -> None:
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    if not __debug__:
        raise SystemExit("Do not run replay with Python optimization (-O)")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("claim", choices=CLAIMS)
    parser.add_argument("--records-only", action="store_true",
                        help="validate historical records without new proof computation")
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                        help="materialized package root (defaults to the parent of replay/)")
    parser.add_argument("--run-dir", type=Path,
                        help="new directory for the disposable source copy and result.json")
    parser.add_argument("--timeout", type=int, default=7200,
                        help="default child process timeout in seconds")
    parser.add_argument("--threads", type=int,
                        help="worker/thread count for independent d7 checks")
    args = parser.parse_args()

    root = args.root.resolve()
    checks.require(root.is_dir(), "repository root does not exist")
    checks.require(args.timeout > 0, "timeout must be positive")
    threads = args.threads if args.threads is not None else (2 if args.claim == "d7-faces" else 4)
    checks.require(threads > 0, "thread count must be positive")
    if args.claim == "d7-spurious":
        checks.require(threads <= 4, "d7-spurious supports 1..4 workers")
    if args.claim == "d7-faces":
        checks.require(threads <= 2, "d7-faces supports at most 2 workers")
    records_only = bool(args.records_only or args.claim in RECORD_ONLY_CLAIMS)
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    run_dir = args.run_dir.resolve() if args.run_dir else root / "work" / "replay-runs" / run_id
    checks.require(not run_dir.exists(), "run directory already exists; choose a fresh path")
    session = ReplaySession(root, run_dir, args.timeout, threads)
    result: dict[str, Any] = {
        "schema": "sic-povm-replay-result-v1",
        "claim": args.claim,
        "mode": "records-only" if records_only else "fresh-execution",
        "started_utc": now_utc(),
        "python": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        "optimized_python": not __debug__,
        "repository_tree_isolated": True,
    }
    error: str | None = None
    baseline_inventory: dict[str, dict[str, Any]] = {}
    source_before: dict[str, dict[str, Any]] = {}
    provenance_summary: dict[str, Any] | None = None
    acceptance: dict[str, Any] | None = None
    explicit_outputs: list[str] = []
    patterns: list[str] = []
    try:
        provenance_summary = checks.verify_provenance(root, claim=args.claim)
        source_before = checks.inventory_tree(root)
        session.create()
        baseline_inventory = checks.inventory_tree(session.workspace, include_work=True)
        # The scratch copy must start byte-for-byte equal to all materialized
        # repository files except excluded VCS, caches, and prior work output.
        checks.require(canonical_hash(baseline_inventory) == canonical_hash(source_before),
                       "fresh work copy does not match the repository input tree")
        result["repository_provenance"] = provenance_summary
        result["source_input_count"] = len(baseline_inventory)
        result["source_tree_sha256"] = canonical_hash(baseline_inventory)
        result["source_inputs"] = relative_inventory(baseline_inventory)
        result["claim_provenance"] = checks.claim_provenance(root, args.claim)
        run_tag = "public_" + run_id.replace("-", "_")
        patterns = output_patterns(args.claim, run_tag) if not records_only else []
        result["fresh_output_targets"] = patterns
        if not records_only:
            session.clear_stale_outputs(patterns)
            result["prior_outputs_removed"] = session.cleared_outputs
        if records_only:
            acceptance = checks.validate_historical_claim(session.workspace, args.claim)
        else:
            acceptance, explicit_outputs = execute_claim(session, args.claim, threads, run_tag)
            for relative in explicit_outputs:
                checks.require((session.workspace / relative).is_file(),
                               "fresh output was not created: " + relative)
        result["commands"] = session.commands
        result["acceptance"] = acceptance
        result["explicit_outputs"] = explicit_outputs
    except Exception as exc:
        error = f"{type(exc).__name__}: {exc}"
        result["commands"] = session.commands

    after_inventory: dict[str, dict[str, Any]] = {}
    if session.workspace.is_dir():
        try:
            after_inventory = checks.inventory_tree(session.workspace, include_work=True)
            result["scratch_output_delta"] = output_delta(baseline_inventory, after_inventory)
            if not records_only:
                validate_write_scope(baseline_inventory, after_inventory, patterns)
                result["preexisting_inputs_unchanged"] = True
            outputs = []
            for relative in explicit_outputs:
                target = session.workspace / relative
                if target.is_file():
                    outputs.append({"path": relative, "sha256": checks.sha256(target),
                                    "bytes": target.stat().st_size})
            if not records_only:
                outputs.extend(declared_output_files(session.workspace, patterns))
            for record in session.commands:
                log_path = session.run_dir / record["log_path"]
                outputs.append({"path": record["log_path"], "sha256": checks.sha256(log_path),
                                "bytes": log_path.stat().st_size})
            result["outputs"] = sorted({item["path"]: item for item in outputs}.values(),
                                       key=lambda item: item["path"])
        except Exception as exc:
            error = error or f"output inventory failed: {type(exc).__name__}: {exc}"

    # Check that the user's materialized inputs stayed unchanged. The run
    # directory is under work/, which is excluded from this source snapshot.
    try:
        source_after = checks.inventory_tree(root)
        checks.require(canonical_hash(source_before) == canonical_hash(source_after),
                       "the repository input tree changed during replay")
        result["input_tree_unchanged"] = True
    except Exception as exc:
        error = error or f"input immutability check failed: {type(exc).__name__}: {exc}"
        result["input_tree_unchanged"] = False

    result["finished_utc"] = now_utc()
    result["status"] = "PASS" if error is None else "FAILED"
    if error is not None:
        result["error"] = error
    result_path = session.run_dir / "result.json"
    if session.run_dir.is_dir():
        result["result_path"] = result_path.relative_to(root).as_posix() if result_path.is_relative_to(root) else "result.json"
        write_result(result_path, result)
        print(json.dumps({
            "status": result["status"],
            "claim": args.claim,
            "mode": result["mode"],
            "result": result["result_path"],
            "workspace": "repo",
            "error": error,
        }, indent=2))
    else:
        print(json.dumps({"status": "FAILED", "claim": args.claim, "error": error}, indent=2))
    return 0 if error is None else 1


if __name__ == "__main__":
    raise SystemExit(main())

