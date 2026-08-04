import json
import os
import tempfile
import unittest

from verifier.check import VerificationError, load_and_check


def call(formula):
    return {"kind": "call", "formula": formula}


def certificate(proof, numerator=2, denominator=1):
    return {
        "format": "maxsat-local-proof-v1",
        "target": {"numerator": numerator, "denominator": denominator},
        "proof": {"kind": "strategy", "formula": proof["formula"], "proof": proof},
    }


class VerifierTests(unittest.TestCase):
    def check_data(self, data):
        handle, name = tempfile.mkstemp(suffix=".json")
        try:
            with os.fdopen(handle, "w") as stream:
                json.dump(data, stream)
            return load_and_check(name)
        finally:
            os.unlink(name)

    def test_semantic_reduction(self):
        parent = [[2], [-2]]
        proof = {
            "kind": "decompose", "transition": "semantic", "formula": parent,
            "alternatives": [{"offset": 1, "decrease": 2, "formula": [], "proof": call([])}],
            "explanation": {"rule": "test"},
        }
        # Explanations are not trusted and are rejected by the minimal schema
        # until the producer omits them from the logical node.
        proof.pop("explanation")
        checker = self.check_data(certificate(proof))
        self.assertEqual(checker.strategies, 1)

    def test_assignment(self):
        parent = [[2, 3], [-2]]
        proof = {
            "kind": "decompose", "transition": "assign", "formula": parent,
            "variable": 2,
            "alternatives": [
                {"offset": 1, "decrease": 2, "formula": [], "proof": call([])},
                {"offset": 1, "decrease": 1, "formula": [[3]], "proof": call([[3]])},
            ],
        }
        self.check_data(certificate(proof))

    def test_grouping_and_absorption_semantically(self):
        # y=false is dominated by y=true.  The remaining x assignments are
        # represented by the fresh variable 3 in the residual formula.
        proof = {
            "kind": "decompose", "transition": "semantic",
            "formula": [[2], [-2], [4]],
            "alternatives": [{
                "offset": 1, "decrease": 1,
                "formula": [[3], [-3]],
                "proof": call([[3], [-3]]),
            }],
        }
        self.check_data(certificate(proof))

    def test_tail_split(self):
        assumed = lambda formula: {"kind": "assumption", "formula": formula,
                                   "name": "test", "vector": [1]}
        proof = {
            "kind": "refine", "rule": "tail_empty_or_nonempty",
            "formula": [[0, 2]], "clause": 0,
            "children": [
                {"kind": "strategy", "formula": [[2]], "proof": assumed([[2]])},
                {"kind": "strategy", "formula": [[1, 2]],
                 "proof": assumed([[1, 2]])},
            ],
        }
        self.check_data({"format":"maxsat-local-proof-v1",
                         "target":{"numerator":2,"denominator":1},
                         "proof":proof})

    def test_canonicalization_keeps_nonempty_tail_typed(self):
        from verifier.formula import canonical_formula
        self.assertNotEqual(canonical_formula([[1], [1, 2]]),
                            canonical_formula([[2], [1, 2]]))

    def test_wrong_reward_rejected(self):
        proof = {
            "kind": "decompose", "transition": "semantic", "formula": [[2]],
            "alternatives": [{"offset": 0, "decrease": 1, "formula": [], "proof": call([])}],
        }
        with self.assertRaises(VerificationError):
            self.check_data(certificate(proof))

    def test_semantic_checks_every_tail_value(self):
        tail = {"tail": 7, "kind": "any"}
        # The claimed child agrees when tail=false but not when tail=true.
        proof = {
            "kind": "decompose", "transition": "semantic",
            "formula": [[tail, 2]],
            "alternatives": [{"offset": 0, "decrease": 0,
                              "formula": [[2]], "proof": call([[2]])}],
        }
        with self.assertRaises(VerificationError):
            self.check_data(certificate(proof))

    def test_assumption_is_reported(self):
        formula = [[2], [-2]]
        proof = {"kind": "assumption", "formula": formula,
                 "name": "lemma-test", "vector": [2]}
        checker = self.check_data(certificate(proof))
        self.assertEqual(checker.assumptions[0]["name"], "lemma-test")

    def test_unknown_node_rejected(self):
        with self.assertRaises(VerificationError):
            self.check_data(certificate({"kind":"magic","formula":[]}))

    def test_zero_progress_rejected(self):
        with self.assertRaises(VerificationError):
            self.check_data(certificate(call([])))

    def test_legacy_claim_rejected(self):
        proof = {"kind":"decompose", "transition":"legacy_claim",
                 "formula":[], "alternatives":[], "legacy_vector":[3, 3]}
        with self.assertRaises(VerificationError):
            self.check_data(certificate(proof))


if __name__ == "__main__":
    unittest.main()
