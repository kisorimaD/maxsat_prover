"""Small generator/assembler/checker round trip, without repository data files."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from stitch_certificate import assemble_certificate
from verifier.check import load_and_check


ROOT = Path(__file__).resolve().parents[1]


class GeneratorTests(unittest.TestCase):
    def test_local_roundtrip(self):
        with tempfile.TemporaryDirectory() as directory:
            cwd = Path(directory)
            result = subprocess.run(
                [str(ROOT / "maxsat_prover"), "interactive"],
                input="set 2\nassumptions off\nadd x 3 2 ANY\nsimple_branch\nexit\n",
                text=True, capture_output=True, cwd=cwd, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            proof = cwd / "proof.json"
            assemble_certificate(cwd / "pre_certificate.jsonl", proof, 2, 1)
            self.assertEqual(load_and_check(proof).assumptions, [])
            command = ["python3", str(ROOT / "verify_certificate.py"), str(proof),
                       str(cwd / "assumptions.json")]
            result = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("ACCEPT LOCAL", result.stdout)
            self.assertIn("q=2, possible_degrees=[]", result.stdout)
            self.assertEqual(json.loads((cwd / "assumptions.json").read_text()), [])

    def test_incomplete_generation_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            cwd = Path(directory)
            result = subprocess.run([str(ROOT / "maxsat_prover"), "interactive"],
                                    input="add x 3 2 ANY\nexit\n", text=True,
                                    capture_output=True, cwd=cwd, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            with self.assertRaisesRegex(ValueError, "missing referenced node"):
                assemble_certificate(cwd / "pre_certificate.jsonl", cwd / "proof.json")
