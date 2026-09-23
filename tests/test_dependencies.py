"""Check that the dependency gate rejects unreviewed changes."""
import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "dependency_gate", Path(__file__).resolve().parents[1] / "scripts/dependencies.py")
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class DependencyGateTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.package = root / "package"
        self.patch = root / "patch"
        self.files = ("Model/Root.lean", "Model/Hash.lean")
        self.package.mkdir()
        for relative in self.files:
            target = self.patch / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(f"patched {relative}\n")
        self.original = self.package / self.files[0]
        self.original.parent.mkdir(parents=True)
        self.original.write_text("original\n")
        (self.package / "other.lean").write_text("unchanged\n")
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=FV", "-c", "user.email=fv@example.invalid",
                 "commit", "-qm", "fixture")
        self.revision = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.package), *args], text=True)

    def run_gate(self, *args, revision=None):
        model = GATE.ModelPatch("Fixture", self.package, self.patch,
                                revision or self.revision, self.files)
        with patch.object(GATE, "PATCHES", (model,)), \
                patch("sys.argv", ["dependencies.py", *args]), \
                contextlib.redirect_stdout(io.StringIO()):
            GATE.main()

    def test_install_and_check(self):
        self.run_gate()
        self.run_gate("--check")
        for relative in self.files:
            self.assertEqual((self.package / relative).read_bytes(),
                             (self.patch / relative).read_bytes())

    def test_check_does_not_install(self):
        with self.assertRaisesRegex(SystemExit, "not installed"):
            self.run_gate("--check")
        self.assertEqual(self.original.read_text(), "original\n")

    def test_wrong_revision(self):
        with self.assertRaisesRegex(SystemExit, "revision"):
            self.run_gate(revision="0" * 40)
        self.assertEqual(self.original.read_text(), "original\n")

    def test_unrelated_change_prevents_all_writes(self):
        (self.package / "other.lean").write_text("changed\n")
        with self.assertRaisesRegex(SystemExit, "Unexpected Fixture change"):
            self.run_gate()
        self.assertEqual(self.original.read_text(), "original\n")

    def test_changed_model_is_not_overwritten(self):
        self.run_gate()
        model = self.package / self.files[-1]
        model.write_text("unreviewed\n")
        with self.assertRaisesRegex(SystemExit, "file contents"):
            self.run_gate()
        self.assertEqual(model.read_text(), "unreviewed\n")

    def test_later_package_failure_prevents_earlier_install(self):
        first = GATE.ModelPatch("First", self.package, self.patch, self.revision, self.files)
        second = first._replace(name="Second", revision="0" * 40)
        with patch.object(GATE, "PATCHES", (first, second)), \
                patch("sys.argv", ["dependencies.py"]):
            with self.assertRaisesRegex(SystemExit, "Second revision"):
                GATE.main()
        self.assertEqual(self.original.read_text(), "original\n")

    def test_staged_change_is_rejected(self):
        self.original.write_text("staged\n")
        self.git("add", str(self.original.relative_to(self.package)))
        with self.assertRaisesRegex(SystemExit, "Unexpected Fixture change"):
            self.run_gate()
        self.assertEqual(self.original.read_text(), "staged\n")


if __name__ == "__main__":
    unittest.main()
