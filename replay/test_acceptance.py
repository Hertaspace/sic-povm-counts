#!/usr/bin/env python3
"""Lightweight acceptance regressions; no CAS, SMT, or full root replay."""
from __future__ import annotations

from copy import deepcopy
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import checks

ROOT = Path(__file__).resolve().parents[1]


class AcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.orbits = checks.load_json(ROOT / "independent/d7-orbits/summary.json")
        spec = importlib.util.spec_from_file_location("faces_test", ROOT / "replay/d7_faces.py")
        cls.faces = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.faces)
        cls.subset = {key: cls.faces.CONES[key] for key in ("l1_16", "l1_72", "l2_128")}

    def test_complete_historical_records(self):
        for claim in ("d4", "d5", "d6", "d7-spurious", "d7-orbits", "ghosts"):
            with self.subTest(claim=claim):
                checks.validate_historical_claim(ROOT, claim)

    def test_overlapping_orbits_are_rejected(self):
        report = deepcopy(self.orbits)
        report["primes"]["673"]["ordinary_orbits"][1]["overlap_previous"] = 1
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d7_orbits(report)

    def test_duplicate_reference_label_is_rejected(self):
        report = deepcopy(self.orbits)
        report["sg_words"][1]["label"] = report["sg_words"][0]["label"]
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d7_orbits(report)

    def test_false_seed_identity_is_rejected(self):
        report = deepcopy(self.orbits)
        report["exact"]["seeds"]["G2"]["q_bad_count"] = 1
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d7_orbits(report)

    def test_wrong_displacement_kernel_is_rejected(self):
        report = deepcopy(self.orbits)
        report["primes"]["953"]["kernel"] = 48
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d7_orbits(report)

    def test_missing_nonhermitian_witness_is_rejected(self):
        report = checks.load_json(ROOT / "sources/exact-d4-d5/certificates/e09_exact_d5.json")
        report["nonHermitian_projector_witness"] = None
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d5_lower(report)

    def test_historical_d6_is_not_fresh(self):
        with self.assertRaises(checks.AcceptanceError):
            checks.check_d6(ROOT, fresh=True)

    def test_corrupt_frozen_member_is_rejected(self):
        source = ROOT / "sources/d7/numerics/e44_d7_second_batch_v1_root_snapshot.json"
        snapshot = checks.load_json(source)
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            shutil.copy(source, directory / source.name)
            name = snapshot["chunks"][0]["file"]
            (directory / name).write_bytes((source.parent / name).read_bytes() + b" ")
            with self.assertRaisesRegex(checks.AcceptanceError, "SHA-256 mismatch"):
                checks.check_frozen_snapshot(directory / source.name)

    def test_original_twelve_face_groups_are_structurally_valid(self):
        self.faces.validate_reports(ROOT / "independent/d7-faces/out", self.subset)

    def test_three_faces_cannot_pass_the_full_48_group_gate(self):
        with self.assertRaises(ValueError):
            self.faces.validate_reports(ROOT / "independent/d7-faces/out")

    def test_consistently_corrupted_face_weight_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "out"
            shutil.copytree(ROOT / "independent/d7-faces/out", out)
            path = out / "l1_16_analysis.json"
            analysis = checks.load_json(path)
            analysis["min_weight"] = "2"
            path.write_text(json.dumps(analysis))
            path = out / "summary.json"
            summary = checks.load_json(path)
            summary["cones"]["l1_16"] = analysis
            path.write_text(json.dumps(summary))
            with self.assertRaisesRegex(ValueError, "incorrect initial face"):
                self.faces.validate_reports(out, self.subset)

    def test_optimized_python_is_rejected(self):
        run = subprocess.run([sys.executable, "-O", str(ROOT / "replay/run.py"), "integrity"],
                             capture_output=True, text=True,
                             env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"), timeout=10)
        self.assertNotEqual(run.returncode, 0)
        self.assertIn("optimization", run.stderr)

    def test_owned_process_group_timeout_is_bounded(self):
        import run as runner
        with tempfile.TemporaryDirectory() as temporary:
            session = runner.ReplaySession(ROOT, Path(temporary) / "job", timeout=1, threads=1)
            session.workspace.mkdir(parents=True)
            session.logs.mkdir()
            # The descendant inherits stdout. A leaked descendant would keep
            # communicate() open; killing the owned group must close it promptly.
            pid_file = Path(temporary) / "owned-pids.json"
            program = ("import json,os,pathlib,subprocess,sys,time; "
                       "desc=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); "
                       f"pathlib.Path({str(pid_file)!r}).write_text(json.dumps([os.getpid(),desc.pid])); "
                       "print('started',flush=True); time.sleep(60)")
            def signal_owned_pids(pid, sig):
                # This test records its own parent and descendant. Signal only
                # those exact PIDs, even when exercising the group-stop branch.
                owned = json.loads(pid_file.read_text())
                self.assertEqual(owned[0], pid)
                for owned_pid in reversed(owned):
                    try:
                        os.kill(owned_pid, sig)
                    except ProcessLookupError:
                        pass
            start = time.monotonic()
            with patch.object(runner.os, "killpg", signal_owned_pids):
                with self.assertRaises(checks.AcceptanceError):
                    session.child("timeout-probe", ["-c", program], timeout=1)
            self.assertTrue(session.commands[-1]["timed_out"])
            self.assertLess(time.monotonic() - start, 10)


class D7FinitenessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location(
            "finiteness_test", ROOT / "independent/d7-finiteness/kill_nf5.py")
        cls.checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.checker)
        cls.block_basis = cls.checker.linear_span_basis(
            cls.checker.block_relation_polys(cls.checker.Weyl(16), [0], [6], 7))

    def reports(self):
        """Minimal complete gate fixture, with distinct grading and weights."""
        roots = [7, 16, 20, 23, 24, 25]
        orbits = [{"size": size, "orbit": orbit, "in_seed_covered": True}
                  for size, orbit in ((7, 48), (14, 48), (14, 48), (20, 336), (21, 16), (21, 48))]
        rows = [{"schema": "portable-unit-cell-v1", "sum_is_1": True,
                 "unmatched_generator_indices": list(range(3284, 3289)),
                 "unmatched_linear_in_block_span": 5, "unmatched_not_explained": [],
                 "grade_weight_mismatches_sample": [14]} for _ in range(21)]
        rows += [{"schema": "portable-unit-circuit-v1", "sum_is_1": True, "step_fail": None,
                  "unmatched_sample": list(range(3284, 3290)),
                  "unmatched_used_generator_indices": list(range(3284, 3289)),
                  "unmatched_linear_in_block_span": 5, "unmatched_not_explained": [],
                  "used_generators_matched_to_model": 16, "n_used_leaves": 21,
                  "n_dependency_missing": 0, "n_declared_extra_leaves": 0,
                  "n_nonhomogeneous_truncated": 0, "nonhomogeneous_generators_sample": [],
                  "grade_weight_mismatches_sample": [14]} for _ in range(4)]
        blocks = [{"mask": mask, "orbit_index": orbit, "n_certificates": count,
                   "n_cells_used": count, "z3": "unsat",
                   "notes": [{"notes": [], "certificate_weight_in_cell": True,
                              "n_cell_entries": 1, "n_cell_polys": 1} for _ in range(count)]}
                  for mask, orbit, count in ((16256, 0, 8), (2097024, 0, 3), (2097024, 1, 3),
                                             (266354560, 0, 3), (266354560, 1, 3),
                                             (268435328, 0, 1), (268435328, 1, 1), (268435328, 2, 1),
                                             (34093399936, 0, 1), (34093399936, 1, 1))]
        blocks.append({"kind": "twenty-element-base", "mask": 267386752, "z3": "unsat"})
        return {
            "self": dict.fromkeys(("tau7_is_1", "reconstruction_7abT", "c_q_equals_Z_minus_q",
                                   "minors_vanish_on_rank1", "squares_vanish_on_rank1", "row_witness_C",
                                   "products_zero_on_row", "z0_zero_on_row", "parse_ty", "parse_prod",
                                   "parse_trace_is_z0sq_minus_8t", "parse_bare_coeff", "parse_pow"), True),
            "n1": {"roots": roots, "n_minor_coefficients": 40131, "n_unit_at_all_six_primes": 40131,
                   "n_positive_at_some_prime": 0, "working_tau": 16,
                   "histogram": {str(r): {"0": 40131} for r in roots}},
            "n2": {"tau": 16, "group_conjugation_order": 336, "abstract_SL2_order": 336,
                   "group_generators_failed": 0, "group_generators_ok": 10,
                   "conjugation_equals_some_SL2_action": True, "base_patterns": 343, "closed_patterns": 2401,
                   "seed_union": 544, "published_union_conjugation": 544, "published_union_abstract": 544,
                   "claimed_blocked": 544, "n_claimed_fail": 0, "claimed_fail_closed_patterns": [],
                   "z3_closed_outside_claimed": "unsat", "seed_orbit_summary": orbits,
                   "published_under_conjugation": orbits, "published_under_abstract_SL2": orbits,
                   "explicit_masks_outside_claimed": []},
            "n3": {"merge_status_field": "PASS", "n": 25, "results": rows},
            "n4": {"n_patterns": 343, "blocks": blocks},
        }

    def accept(self, reports):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for stage, report in reports.items():
                (directory / (stage + ".json")).write_text(json.dumps(report))
            return checks.check_d7_finiteness(directory, fresh=True)

    def test_explained_relations_and_distinct_grading_are_accepted(self):
        self.assertEqual(self.accept(self.reports())["unit_identities"], 25)

    def test_unexplained_generator_is_rejected(self):
        for index in (0, 21):
            with self.subTest(index=index):
                reports = self.reports()
                reports["n3"]["results"][index]["unmatched_not_explained"] = [3284]
                with self.assertRaisesRegex(checks.AcceptanceError, "unexplained"):
                    self.accept(reports)

    def test_missing_or_incomplete_span_check_is_rejected(self):
        for index in (0, 21):
            for key, value in (("unmatched_not_explained", None),
                               ("unmatched_linear_in_block_span", 4),
                               ("unmatched_linear_in_block_span", None)):
                with self.subTest(index=index, key=key, value=value):
                    reports = self.reports()
                    reports["n3"]["results"][index][key] = value
                    with self.assertRaisesRegex(checks.AcceptanceError, "unverified"):
                        self.accept(reports)

    def test_circuit_audit_cannot_use_the_truncated_sample(self):
        reports = self.reports()
        row = reports["n3"]["results"][21]
        row["unmatched_used_generator_indices"] = list(range(100, 135))
        row["unmatched_sample"] = list(range(100, 130))
        row["unmatched_linear_in_block_span"] = 30
        row["n_used_leaves"] = 51
        with self.assertRaisesRegex(checks.AcceptanceError, "unverified"):
            self.accept(reports)
        row["unmatched_linear_in_block_span"] = 35
        self.assertEqual(self.accept(reports)["circuit_identities"], 4)
        row["used_generators_matched_to_model"] = 15
        with self.assertRaisesRegex(checks.AcceptanceError, "every used leaf"):
            self.accept(reports)

    def test_unknown_weight_cover_is_rejected(self):
        reports = self.reports()
        reports["n4"]["blocks"][0]["z3"] = "unknown"
        with self.assertRaisesRegex(checks.AcceptanceError, "not UNSAT"):
            self.accept(reports)

    def test_exact_block_span_distinguishes_changed_and_nonlinear_generators(self):
        for text in ("1+13*z13", "z8+5*z13", "2*z8+10*z13"):
            self.assertTrue(self.checker.linear_in_span(self.checker.parse_poly(text), self.block_basis))
        for text in ("1+14*z13", "z8+6*z13", "z8*z13", "t", "y"):
            self.assertFalse(self.checker.linear_in_span(self.checker.parse_poly(text), self.block_basis))

    def test_circuit_authenticates_all_used_leaves_beyond_legacy_sample(self):
        for start in (100, 3258):
            with self.subTest(start=start):
                used = list(range(start, start + 35))
                generators = ["0"] * (used[-1] + 1)
                for i in used:
                    generators[i] = "z8+5*z13"
                generators[used[-1]] = "z8+6*z13"
                cert = {"original_generators": generators, "preprocessing": {"operations": []},
                        "reduced_members": [{"row_index_zero_based": i, "multiplier": "1"} for i in used],
                        "source_generator_indices_zero_based": used}
                table = {self.checker.poly_hash({}): [("zero", None, "full")]}
                row = self.checker.replay_circuit(cert, table, {8: 0, 13: 0}, self.block_basis, set())
                self.assertEqual(len(row["unmatched_sample"]), 0 if start == 100 else 30)
                self.assertEqual(row["unmatched_used_generator_indices"], used)
                self.assertEqual(row["unmatched_linear_in_block_span"], 34)
                self.assertEqual(row["unmatched_not_explained"], [used[-1]])


if __name__ == "__main__":
    unittest.main(verbosity=2)
