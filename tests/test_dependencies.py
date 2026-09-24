"""Check that the dependency gate rejects unreviewed changes."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "dependency_gate", Path(__file__).resolve().parents[1] / "scripts/dependencies.py")
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class DependencyGateTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.package = Path(self.temp.name)
        self.source = self.package / "Model.lean"
        self.source.write_text("original\n")
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=FV", "-c", "user.email=fv@example.invalid",
                 "commit", "-qm", "fixture")
        self.model = GATE.Dependency("Fixture", self.package, self.git("rev-parse", "HEAD").strip())

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.package), *args], text=True)

    def test_clean_dependency(self):
        GATE.check_dependency(self.model)

    def test_missing_dependency(self):
        with self.assertRaisesRegex(SystemExit, "Missing Fixture"):
            GATE.check_dependency(self.model._replace(package=self.package / "missing"))

    def test_wrong_revision(self):
        with self.assertRaisesRegex(SystemExit, "revision"):
            GATE.check_dependency(self.model._replace(revision="0" * 40))

    def test_modified_file(self):
        self.source.write_text("changed\n")
        with self.assertRaisesRegex(SystemExit, "local changes"):
            GATE.check_dependency(self.model)
        self.assertEqual(self.source.read_text(), "changed\n")

    def test_untracked_file(self):
        (self.package / "Extra.lean").write_text("unreviewed\n")
        with self.assertRaisesRegex(SystemExit, "local changes"):
            GATE.check_dependency(self.model)

    def test_staged_change(self):
        self.source.write_text("staged\n")
        self.git("add", "Model.lean")
        with self.assertRaisesRegex(SystemExit, "local changes"):
            GATE.check_dependency(self.model)


if __name__ == "__main__":
    unittest.main()
