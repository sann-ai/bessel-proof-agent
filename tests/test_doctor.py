"""Read-only setup diagnostics for a clone and a source ZIP."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts.doctor import inspect


class DoctorTests(unittest.TestCase):
    def make_root(self, directory):
        root = Path(directory)
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        (root / "lakefile.toml").write_text('[[require]]\nname="mathlib"\nrev="pinned"\n')
        (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "rev": "pinned"}]}))
        return root

    def test_zip_root_needs_no_project_git_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_root(directory)
            (root / ".lake/packages/mathlib").mkdir(parents=True)
            output = root / ".lake/build/lib/lean/BesselProofAgent.olean"
            output.parent.mkdir(parents=True)
            output.touch()
            def version(command, root):
                self.assertNotIn("--install", command)
                return True, "pinned" if "rev-parse" in command else "version"
            with patch("scripts.doctor.shutil.which", side_effect=lambda name: name), \
                 patch("scripts.doctor.run", side_effect=version):
                self.assertTrue(all(ok for ok, _ in inspect(root)))
            self.assertFalse((root / ".git").exists())

    def test_missing_tools_and_cache_report_preparation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_root(directory)
            with patch("scripts.doctor.shutil.which", return_value=None), patch("scripts.doctor.run") as run:
                checks = inspect(root)
            self.assertFalse(all(ok for ok, _ in checks))
            run.assert_not_called()
            self.assertFalse((root / ".lake").exists())

    def test_manifest_and_checkout_mismatches_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_root(directory)
            (root / "lakefile.toml").write_text('[[require]]\nname="mathlib"\nrev="different"\n')
            (root / ".lake/packages/mathlib").mkdir(parents=True)
            with patch("scripts.doctor.shutil.which", side_effect=lambda name: name), \
                 patch("scripts.doctor.run", return_value=(True, "wrong-checkout")):
                checks = inspect(root)
            failures = [message for ok, message in checks if not ok]
            self.assertTrue(any("mathlib 固定版" in message for message in failures))
            self.assertTrue(any("依存コミット" in message for message in failures))

    def test_missing_toolchain_is_reported_without_installing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.make_root(directory)
            with patch("scripts.doctor.shutil.which", side_effect=lambda name: name), \
                 patch("scripts.doctor.run", return_value=(False, "not installed")) as run:
                checks = inspect(root)
            self.assertTrue(any(not ok and "not installed" in message for ok, message in checks))
            self.assertTrue(all("--install" not in call.args[0] for call in run.call_args_list))
