"""Check that reverse imports cannot pass the layer check."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
from layers import check_layers, imports


class LayerTests(unittest.TestCase):
    def check(self, sources):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, source in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            return check_layers(root)

    def test_forward_imports(self):
        self.assertEqual(self.check({
            "semantics/Model.lean": "import Solm.Semantics\n",
            "invariants/Safe.lean": "import semantics.Model\n",
            "proofs/nested/Safe.lean": "import semantics.Model invariants.Safe\n",
        }), [])

    def test_reverse_imports(self):
        for source, target in (("semantics", "invariants"),
                               ("semantics", "proofs"), ("invariants", "proofs")):
            with self.subTest(source=source, target=target):
                errors = self.check({
                    f"{source}/A.lean": f"import {target}.B\n",
                    f"{target}/B.lean": "",
                })
                self.assertEqual(len(errors), 1)
                self.assertIn("forbidden import", errors[0])

    def test_stale_module(self):
        errors = self.check({"proofs/A.lean": "import invariants.OldName\n"})
        self.assertEqual(errors, ["proofs.A: missing module invariants.OldName"])

    def test_module_import_modifiers(self):
        for declaration in ("public import", "public meta import", "meta import all"):
            with self.subTest(declaration=declaration):
                errors = self.check({
                    "semantics/A.lean": f"module\n{declaration} proofs.B\n",
                    "proofs/B.lean": "",
                })
                self.assertEqual(errors, ["semantics.A: forbidden import proofs.B"])

    def test_comments_and_multiple_imports(self):
        self.assertEqual(list(imports("""
/- import proofs.Hidden
   /- nested -/ import proofs.HiddenToo -/
import semantics.Model /- note -/ semantics.Storage -- note
-- import proofs.HiddenThree
import invariants.Safe
""")), ["semantics.Model", "semantics.Storage", "invariants.Safe"])


if __name__ == "__main__":
    unittest.main()
