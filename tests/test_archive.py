import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from bessel_agent import archive
from bessel_agent.core import InputError, ROOT, _diagnostics, load_json, verify
from bessel_agent.parser import parse_identity


def target(conditions="n integer, x>0"):
    return parse_identity("J_n(-x)=(-1)^n*J_n(x)", conditions)


def request():
    return {**target(), "proof": {"mode": "direct", "recipe": "bessel"}}


class ArchiveBoundaryTests(unittest.TestCase):
    def test_canonical_hash_tracks_conditions_and_exact_ast_only(self):
        original = target("n integer,x>1,x<3")
        changed_order = copy.deepcopy(original)
        changed_order["extra_conditions"].reverse()
        changed_order["extra_conditions"][1] = {"op": "compare", "variable": "x", "relation": "gt",
                                                 "value": {"numerator": 1, "denominator": 1}}
        self.assertEqual(archive.target_hash(original), archive.target_hash(changed_order))
        self.assertNotEqual(archive.target_hash(original), archive.target_hash(target("n integer,x>2,x<3")))
        swapped = {**original, "lhs": original["rhs"], "rhs": original["lhs"]}
        self.assertNotEqual(archive.target_hash(original), archive.target_hash(swapped))
        with_proof = {**original, "proof": {"mode": "direct", "recipe": "ring"}}
        self.assertEqual(archive.target_hash(original), archive.target_hash(with_proof))

    def test_roots_are_separate_and_reading_does_not_create_default_data(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            first, second, missing = (base / name for name in ("first", "second", "missing"))
            with patch.dict(os.environ, {"BESSEL_ARCHIVE_DIR": str(missing)}):
                self.assertEqual(archive.list_records(), [])
                self.assertFalse(missing.exists())
                self.assertEqual(archive.resolve_archive_root(first), first.resolve())
            archive.register_failure({"status": "unresolved", "reason": "pending"}, first, request=target())
            self.assertEqual(len(archive.list_records(first)), 1)
            self.assertEqual(archive.list_records(second), [])
            self.assertFalse(second.exists())
        with self.assertRaises(InputError):
            archive.resolve_archive_root(ROOT / "private-archive")

    def test_failure_input_candidate_provenance_and_repeated_attempts_survive(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / "archive"
            first = archive.register_failure({"status": "needs_conditions", "reason": "missing x domain"}, root,
                                             original_input="J_n(x)=0; n integer", input_conditions="n integer",
                                             candidate={"mode": "direct", "recipe": "sorry"}, request=target(),
                                             provenance={"route": "direct", "attempt": 1})
            second = archive.register_failure({"status": "unresolved", "reason": "rejected plan"}, root,
                                              original_input="J_n(-x)=(-1)^n J_n(x)", request=target())
            self.assertNotEqual(first["id"], second["id"])
            self.assertEqual(len(archive.find_exact(target(), root)), 2)
            self.assertEqual(archive.show_record(first["id"], root)["candidate"]["recipe"], "sorry")
            self.assertEqual((Path(first["record_dir"]) / "original_input.txt").read_text(), "J_n(x)=0; n integer")
            self.assertIn("条件", (Path(first["record_dir"]) / "detail.md").read_text())
            self.assertEqual(len(archive.search_records("needs_conditions", root)), 1)
            self.assertEqual(len(json.loads((root / "index.json").read_text())["records"]), 2)
            self.assertTrue((root / "catalog.md").exists())

    def test_bad_index_is_reconstructed_but_changed_evidence_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            record = archive.register_failure({"status": "unresolved", "reason": "test"}, root, request=target())
            (root / "index.json").write_text('{"malicious":')
            self.assertEqual(archive.list_records(root)[0]["id"], record["id"])
            self.assertEqual(json.loads((root / "index.json").read_text())["schema_version"], 1)
            (Path(record["record_dir"]) / "request.json").write_text("{}")
            with self.assertRaisesRegex(InputError, "changed"):
                archive.list_records(root)
            with self.assertRaises(InputError):
                archive.find_exact(target(), root)

    def test_accepted_registration_replays_snapshot_and_is_atomic(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            verification = base / "verified"
            with patch("bessel_agent.core._run_lean", return_value={"accepted": True, "axioms": []}):
                verify(request(), verification)
            with patch("bessel_agent.archive.replay", return_value={"status": "unresolved", "replayed": False}) as checked:
                with self.assertRaisesRegex(InputError, "replay"):
                    archive.register_verification(verification, base / "archive")
                snapshot = checked.call_args.args[0]
                self.assertNotEqual(snapshot, verification)
            self.assertEqual(list((base / "archive" / "entries").iterdir()), [])
            with patch("bessel_agent.archive.replay", return_value={"status": "proved", "replayed": True}):
                record = archive.register_verification(verification, base / "archive")
            self.assertEqual(record["status"], "proved")
            with patch("bessel_agent.archive.replay", return_value={"status": "proved", "replayed": True}) as checked:
                self.assertTrue(archive.replay_record(record["id"], base / "archive")["replayed"])
                checked.assert_called_once()
            with patch("bessel_agent.core.environment", return_value={"changed": "environment"}), patch("bessel_agent.core._run_lean") as lean:
                with self.assertRaisesRegex(InputError, "environment|foundation"):
                    archive.replay_record(record["id"], base / "archive")
                lean.assert_not_called()

    def test_forged_certificates_and_environment_mismatch_are_rejected_before_lean(self):
        for tamper in ("certificate", "environment"):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                verification = base / "verified"
                with patch("bessel_agent.core._run_lean", return_value={"accepted": True, "axioms": []}):
                    verify(request(), verification)
                if tamper == "certificate":
                    (verification / "certificate.lean").write_text("axiom forged : False\n")
                else:
                    result = load_json(verification / "result.json")
                    result["environment"] = {"lean-toolchain": "changed"}
                    (verification / "result.json").write_text(json.dumps(result))
                with patch("bessel_agent.core._run_lean") as lean:
                    with self.assertRaises(InputError):
                        archive.register_verification(verification, base / "archive")
                    lean.assert_not_called()
                self.assertEqual(list((base / "archive" / "entries").iterdir()), [])

    def test_failed_validation_keeps_request_and_can_be_imported(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            invalid = request()
            invalid["assumptions"] = []
            with patch("bessel_agent.core._run_lean") as lean:
                verify(invalid, base / "verification")
                record = archive.register_verification(base / "verification", base / "archive", original_input="J_n(x)=0")
            lean.assert_not_called()
            self.assertEqual(record["status"], "needs_conditions")
            self.assertEqual(record["request"], invalid)
            self.assertIsNone(record["target_sha256"])

    def test_malformed_source_status_is_rejected_without_registering(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            source = base / "verification"
            source.mkdir()
            (source / "result.json").write_text('{"status": {"unexpected": "value"}}')
            with self.assertRaises(InputError):
                archive.register_verification(source, base / "archive")
            self.assertEqual(list((base / "archive" / "entries").iterdir()), [])

    def test_ids_and_symlinks_cannot_escape_the_archive(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / "archive"
            record = archive.register_failure({"status": "unresolved"}, root, request=target())
            with self.assertRaises(InputError):
                archive.show_record("../../outside", root)
            candidate = Path(record["record_dir"]) / "request.json"
            candidate.unlink()
            candidate.symlink_to(ROOT / "examples/direct.json")
            with self.assertRaises(InputError):
                archive.show_record(record["id"], root)

    def test_cli_archives_failed_parse_and_preserves_successful_parse_json(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            source = base / "input.txt"
            root = base / "archive"
            source.write_text("J_n(x)=0; n integer")
            command = [sys.executable, "-m", "bessel_agent", "parse", str(source), "--archive", "--archive-dir", str(root)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            failure = json.loads(result.stdout)
            self.assertEqual(failure["status"], "needs_conditions")
            record = archive.show_record(failure["archive_id"], root)
            self.assertEqual((Path(record["record_dir"]) / "original_input.txt").read_text(), source.read_text())
            source.write_text("J_n(-x)=(-1)^n J_n(x); n integer,x>0")
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=True)
            self.assertEqual(json.loads(result.stdout), target())
            self.assertEqual(len(archive.list_records(root)), 2)
            result = subprocess.run([sys.executable, "-m", "bessel_agent", "archive", "list", "--archive-dir", str(root)],
                                    cwd=ROOT, capture_output=True, text=True, check=True)
            self.assertEqual(len(json.loads(result.stdout)), 2)

    def test_verify_cli_archives_validation_failure_and_requires_opt_in(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            source = base / "input.json"
            root = base / "archive"
            data = request()
            data["assumptions"] = []
            source.write_text(json.dumps(data))
            command = [sys.executable, "-m", "bessel_agent", "verify", str(source), "--output", str(base / "verification"),
                       "--archive", "--archive-dir", str(root)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            saved = json.loads(result.stdout)
            self.assertEqual(saved["status"], "needs_conditions")
            self.assertEqual(archive.show_record(saved["archive_id"], root)["original_input"], source.read_text())
            command.remove("--archive")
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("requires --archive", result.stderr)

    def test_diagnostics_remove_local_paths_without_changing_audit_text(self):
        source = Path.home() / "private-run" / "proof_attempt.lean"
        message = f"{source}:4: error\n{ROOT}/BesselProofAgent.lean\n{Path.home()}/.config\nBESSEL_AUDIT_BEGIN"
        cleaned = _diagnostics(message, source)
        self.assertNotIn(str(Path.home()), cleaned)
        self.assertNotIn(str(ROOT), cleaned)
        self.assertIn("proof_attempt.lean:4", cleaned)
        self.assertIn("BESSEL_AUDIT_BEGIN", cleaned)

    def test_nonfinite_json_constants_are_rejected_and_original_input_is_archived(self):
        for constant in ("NaN", "Infinity", "-Infinity", "1e400", "-1e400"):
            with self.subTest(constant=constant), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                source = base / "input.json"
                raw = json.dumps(request()).replace('"value": -1', '"value": ' + constant)
                source.write_text(raw)
                with self.assertRaisesRegex(InputError, "Non-finite JSON"):
                    load_json(source)
                root = base / "archive"
                result = subprocess.run([sys.executable, "-m", "bessel_agent", "verify", str(source),
                                         "--output", str(base / "verification"), "--archive", "--archive-dir", str(root)],
                                        cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2, result.stderr)
                saved = json.loads(result.stdout)
                self.assertEqual(saved["status"], "unresolved")
                self.assertNotIn("archive_error", saved)
                record = archive.show_record(saved["archive_id"], root)
                self.assertEqual(record["original_input"], raw)
                self.assertIsNone(record["request"])
                self.assertIn("Non-finite JSON", record["result"]["detail"])
                self.assertFalse((base / "verification").exists())
        with tempfile.TemporaryDirectory() as folder:
            source = Path(folder) / "metadata.json"
            source.write_text('{"elapsed_seconds": 0.125, "large_finite": 1e300}')
            self.assertEqual(load_json(source), {"elapsed_seconds": 0.125, "large_finite": 1e300})


@unittest.skipUnless(os.environ.get("BESSEL_RUN_LEAN_TESTS") == "1", "Enable real Lean integration checks.")
class ArchiveLeanTests(unittest.TestCase):
    def test_proof_and_refutation_are_replayed_when_imported_and_read(self):
        for name, expected in (("direct.json", "proved"), ("refuted.json", "refuted")):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                data = load_json(ROOT / "examples" / name)
                result = verify(data, base / "verification")
                self.assertEqual(result["status"], expected)
                record = archive.register_verification(base / "verification", base / "archive")
                self.assertEqual(record["status"], expected)
                self.assertTrue(archive.replay_record(record["id"], base / "archive")["replayed"])
                self.assertEqual(archive.find_exact(data, base / "archive")[0]["id"], record["id"])
                changed = {**data, "extra_conditions": [{"op": "x_gt", "value": 1}]}
                self.assertEqual(archive.find_exact(changed, base / "archive"), [])
