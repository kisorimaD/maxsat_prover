import json
import os
import tempfile
import unittest

from verifier.check import Checker, VerificationError, load_and_check


def call(formula):
    return {"kind": "call", "formula": formula}


def certificate(proof, numerator=2, denominator=1):
    return {
        "format": "maxsat-local-proof-v2",
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
        with self.assertRaisesRegex(VerificationError, "invalid decomposition fields"):
            self.check_data(certificate(proof))
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
        tail = {"tail": 0, "kind": "any"}
        nonempty = {"tail": 0, "kind": "nonempty"}
        def strategy(formula):
            proof = {"kind": "decompose", "transition": "semantic", "formula": formula,
                     "alternatives": [{"offset": 1, "decrease": 1,
                                       "formula": [], "proof": call([])}]}
            return {"kind": "strategy", "formula": formula, "proof": proof}
        proof = {
            "kind": "refine", "rule": "tail_empty_or_nonempty",
            "formula": [[tail, 2]], "clause": 0,
            "children": [strategy([[2]]), strategy([[nonempty, 2]])],
        }
        self.check_data({"format": "maxsat-local-proof-v2",
                         "target": {"numerator": 2, "denominator": 1}, "proof": proof})
        proof["children"].pop()
        with self.assertRaisesRegex(VerificationError, "coverage mismatch"):
            self.check_data({"format": "maxsat-local-proof-v2",
                             "target": {"numerator": 2, "denominator": 1}, "proof": proof})

    def test_canonicalization_keeps_nonempty_tail_typed(self):
        from verifier.formula import canonical_formula
        tail = {"tail": 0, "kind": "nonempty"}
        self.assertNotEqual(canonical_formula([[tail], [tail, 2]]),
                            canonical_formula([[2], [tail, 2]]))

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
                 "name": "lemma3", "vector": [1, 8]}
        checker = self.check_data(certificate(proof))
        self.assertEqual(checker.assumptions[0]["name"], "lemma3")

    def test_imported_reduction_can_make_an_enclosing_branch_too_expensive(self):
        tail = {"tail": 0, "kind": "any"}
        cases = (
            ("lemma2", [3, 5], [[3, tail]] * 3 + [[-3, 4, 5]]),
            ("lemma4", [3, 5], [[3], [3, tail], [3, tail], [-3, tail], [-3, tail]]),
            ("double_lemma3", [2, 9, 8], [[3, tail], [3, tail], [-3],
                                          [4, tail], [4, tail], [-4]]),
        )
        for name, vector, formula in cases:
            with self.subTest(name=name):
                assumption = {"kind": "assumption", "name": name,
                              "formula": formula, "vector": vector}
                proof = {
                    "kind": "decompose", "transition": "assign", "variable": 2,
                    "formula": formula + [[2, tail], [2, tail], [-2, tail]],
                    "alternatives": [
                        {"offset": 2, "decrease": 2, "formula": formula,
                         "proof": call(formula)},
                        {"offset": 1, "decrease": 1, "formula": formula,
                         "proof": assumption},
                    ],
                }
                # At 7/5 the branching-only bound passes for each import.
                # The reduction alternative gives (2,2), whose weight is 50/49.
                with self.assertRaisesRegex(VerificationError, r"\[2, 2\] violates"):
                    self.check_data(certificate(proof, 7, 5))

    def test_unknown_import_rejected(self):
        proof = {"kind": "assumption", "formula": [[2]],
                 "name": "not_a_known_lemma", "vector": [100]}
        with self.assertRaisesRegex(VerificationError, "unknown imported lemma"):
            self.check_data(certificate(proof))

    def test_invalid_target_rejected_before_traversal(self):
        for numerator, denominator in ((True, 1), (2.0, 1), (2, False), (1, 1)):
            with self.subTest(target=(numerator, denominator)), self.assertRaises(ValueError):
                Checker(numerator, denominator)

    def test_bottleneck_profile_rejects_other_target_root_and_degrees(self):
        root = [[2, {"tail": i, "kind": "any"}] for i in range(3)]
        root += [[-2, {"tail": i, "kind": "any"}] for i in range(3, 5)]
        proof = {"kind": "refine", "rule": "expose_at_clause", "formula": root,
                 "clause": 3, "variable": 3, "degrees": [[3, 2, False]], "children": []}
        with self.assertRaisesRegex(VerificationError, "bottleneck target"):
            Checker(2, 1, bottleneck=True).check(proof)
        with self.assertRaisesRegex(VerificationError, "bottleneck root"):
            Checker(12872, 10000, bottleneck=True).check(call([[2]]))
        with self.assertRaisesRegex(VerificationError, "five baseline degree classes"):
            Checker(12872, 10000, bottleneck=True).check(proof)

    def test_numeric_tail_shorthand_rejected(self):
        from verifier.formula import normalize_formula
        for literal in (0, 1, -1):
            with self.subTest(literal=literal), self.assertRaises(ValueError):
                normalize_formula([[literal]])

    def test_old_format_rejected(self):
        data = certificate(call([]))
        data["format"] = "maxsat-local-proof-v1"
        with self.assertRaisesRegex(VerificationError, "unknown certificate format"):
            self.check_data(data)

    def test_step51_assignment_in_both_polarities(self):
        from verifier.formula import assignment_residual, normalize_formula
        for sign in (1, -1):
            formula = [[sign * 2, {"tail": i, "kind": "any"}] for i in range(3)]
            formula += [[-sign * 2], [-sign * 2, {"tail": 3, "kind": "any"}]]
            proof = {"kind": "decompose", "transition": "assign", "formula": formula,
                     "variable": 2, "alternatives": []}
            for value in (True, False):
                residual, offset, decrease = assignment_residual(normalize_formula(formula), 2, value)
                self.assertEqual(residual, ())
                proof["alternatives"].append({"offset": offset, "decrease": decrease,
                                               "formula": [], "proof": call([])})
            self.assertEqual(sorted(a["decrease"] for a in proof["alternatives"]), [2, 4])
            self.assertEqual(self.check_data(certificate(proof, 12872, 10000)).assumptions, [])
            proof["alternatives"][0]["decrease"] += 1
            with self.assertRaisesRegex(VerificationError, "assignment alternative"):
                self.check_data(certificate(proof, 12872, 10000))

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
