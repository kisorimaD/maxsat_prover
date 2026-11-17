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


def bounded_certificate(proof, maximum_clause_size, numerator=2, denominator=1):
    return {
        "format": "maxsat-local-proof-v3",
        "maximum_clause_size": maximum_clause_size,
        "scope": {
            "kind": "local_template_family",
            "degree_coverage": "certificate_premise",
        },
        "target": {"numerator": numerator, "denominator": denominator},
        "proof": {"kind": "strategy", "formula": proof["formula"], "proof": proof},
    }


def occurrence_bounded_certificate(
        proof, maximum_variable_occurrences, numerator=2, denominator=1):
    return {
        "format": "maxsat-local-proof-v4",
        "maximum_clause_size": -1,
        "maximum_variable_occurrences": maximum_variable_occurrences,
        "scope": {
            "kind": "local_template_family",
            "degree_coverage": "certificate_premise",
        },
        "target": {"numerator": numerator, "denominator": denominator},
        "proof": {"kind": "strategy", "formula": proof["formula"],
                  "proof": proof},
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

    def test_overlapping_semantic_groups_count_both_costs(self):
        # x=0 and y=0 overlap. The omitted x=y=1 assignments are tied
        # with represented ones because both polarities are unit clauses.
        first = [[3], [-3], [4]]
        second = [[2], [-2], [4]]
        proof = {
            "kind": "decompose", "transition": "semantic",
            "formula": [[2], [-2], [3], [-3], [4]],
            "alternatives": [
                {"offset": 1, "decrease": 2, "formula": first,
                 "proof": call(first)},
                {"offset": 1, "decrease": 2, "formula": second,
                 "proof": call(second)},
            ],
        }
        self.check_data(certificate(proof, 3, 2))
        # The recurrence includes both alternatives: 2*q^-2 > 1 at q=7/5.
        with self.assertRaises(VerificationError):
            self.check_data(certificate(proof, 7, 5))

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

    def test_bounded_assumption_is_rejected(self):
        formula = [[2], [-2]]
        proof = {"kind": "assumption", "formula": formula,
                 "name": "lemma-test", "vector": [2]}
        with self.assertRaisesRegex(VerificationError,
                                    "assumptions are forbidden"):
            self.check_data(bounded_certificate(proof, 3))

    def test_occurrence_bounded_formula_is_accepted(self):
        formula = [[2], [2], [-2]]
        proof = {"kind": "decompose", "transition": "semantic",
                 "formula": formula,
                 "alternatives": [{"offset": 2, "decrease": 3,
                                   "formula": [], "proof": call([])}]}
        checker = self.check_data(occurrence_bounded_certificate(proof, 3))
        self.assertEqual(checker.maximum_variable_occurrences, 3)

    def test_occurrence_bound_rejects_explicit_variable(self):
        formula = [[2], [2], [-2], [-2]]
        proof = {"kind": "call", "formula": formula}
        with self.assertRaisesRegex(VerificationError,
                                    "variable 2 occurs 4 times"):
            self.check_data(occurrence_bounded_certificate(proof, 3))

    def test_occurrence_bound_rejects_variable_in_semantic_child(self):
        parent = [[2], [-2], [3], [-3]]
        child = [[4], [-4], [4], [-4]]
        proof = {"kind": "decompose", "transition": "semantic",
                 "formula": parent,
                 "alternatives": [{"offset": 0, "decrease": 0,
                                   "formula": child,
                                   "proof": call(child)}]}
        with self.assertRaisesRegex(VerificationError,
                                    "variable 4 occurs 4 times"):
            self.check_data(occurrence_bounded_certificate(proof, 3))

    def test_occurrence_bound_rejects_duplicated_tail(self):
        tail = {"tail": 7, "kind": "any"}
        formula = [[2, tail], [-2, tail]]
        proof = {"kind": "call", "formula": formula}
        with self.assertRaisesRegex(VerificationError,
                                    "tail literal 7 is duplicated"):
            self.check_data(occurrence_bounded_certificate(proof, 3))

    def test_occurrence_bound_rejects_exposure_degree(self):
        from verifier.refine import expected_children
        node = {"rule": "expose_at_clause",
                "formula": [[2, {"tail": 9, "kind": "any"}]],
                "clause": 0, "variable": 3,
                "degrees": [[3, 1, False]]}
        with self.assertRaisesRegex(ValueError,
                                    "exposure degree exceeds"):
            expected_children(node, maximum_variable_occurrences=3)

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

    def test_score_limit(self):
        from verifier.formula import normalize_formula, MAX_CLAUSES
        from verifier.semantic import optimum_vector
        formula = normalize_formula([[2]] * MAX_CLAUSES)
        self.assertEqual(int(optimum_vector(formula, [])[0]), MAX_CLAUSES)
        with self.assertRaises(ValueError):
            normalize_formula([[2]] * (MAX_CLAUSES + 1))
        with self.assertRaises(ValueError):
            optimum_vector(((2,),) * (MAX_CLAUSES + 1), [])

    def test_tautological_clause_is_rejected_as_unnormalized(self):
        from verifier.formula import normalize_formula, ordered_formula
        for parser in (normalize_formula, ordered_formula):
            with self.subTest(parser=parser.__name__), \
                    self.assertRaisesRegex(ValueError, "tautological clause"):
                parser([[2, -2]])

    def test_invalid_offsets_rejected(self):
        for offset in (-1, True, 1.0, 65537):
            with self.subTest(offset=offset), self.assertRaises(VerificationError):
                proof = {"kind": "decompose", "transition": "semantic", "formula": [[2]],
                         "alternatives": [{"offset": offset, "decrease": 1,
                                           "formula": [], "proof": call([])}]}
                self.check_data(certificate(proof))

    def test_inferred_offset_does_not_wrap(self):
        from verifier.formula import MAX_CLAUSES
        # True pointwise difference is -32767, not a nonnegative reward.
        child = [[2]] * MAX_CLAUSES
        proof = {"kind": "decompose", "transition": "semantic", "formula": [],
                 "alternatives": [{"offset": "infer", "decrease": -MAX_CLAUSES,
                                   "formula": child, "proof": call(child)}]}
        with self.assertRaises(VerificationError):
            self.check_data(certificate(proof))

    def test_nonempty_tail_exposure_has_no_empty_child(self):
        from verifier.refine import expected_children
        from verifier.formula import variables
        node = {"rule": "expose_at_clause", "formula": [[2, {"tail": 9, "kind": "nonempty"}]],
                "clause": 0, "variable": 3, "degrees": [[3, 1, True]]}
        children = expected_children(node)
        self.assertTrue(children)
        self.assertTrue(all(3 in variables(child) for child in children))
        self.assertTrue(any((3,) not in child and (-3,) in child for child in children))
        node["formula"][0][1]["kind"] = "any"
        self.assertIn(((2,),), expected_children(node))

    def test_exposure_preconditions(self):
        from verifier.refine import expected_children
        node = {"rule": "expose_at_clause", "formula": [[2, {"tail": 9, "kind": "any"}]],
                "clause": 0, "variable": 2}
        with self.assertRaises(ValueError):
            expected_children(node)
        node["variable"] = 3
        node["degrees"] = [[1, 3, True]]
        with self.assertRaises(ValueError):
            expected_children(node)
        node["degrees"] = [[3, 1, True]]
        node["formula"] = [[{"tail": 9, "kind": "any"}]]
        with self.assertRaises(ValueError):
            expected_children(node)

    def test_unconditional_exposure_is_not_refinement(self):
        from verifier.refine import expected_children
        node = {"rule": "expose_variable", "formula": [[2], [-2]],
                "variable": 3, "positive": 1, "negative": 1, "singleton": False}
        with self.assertRaises(ValueError):
            expected_children(node)

    def test_bounded_width_normalization(self):
        from verifier.refine import enforce_maximum_clause_size
        any_tail = {"tail": 9, "kind": "any"}
        nonempty_tail = {"tail": 9, "kind": "nonempty"}
        self.assertEqual(
            enforce_maximum_clause_size([[2, 3, 4, any_tail]], 3),
            ((2, 3, 4),))
        self.assertIsNone(
            enforce_maximum_clause_size([[2, 3, 4, nonempty_tail]], 3))
        self.assertIsNone(enforce_maximum_clause_size([[2, 3, 4, 5]], 3))

    def test_bounded_exposure_children(self):
        from verifier.formula import is_tail
        from verifier.refine import expected_children, generate_exposure
        roots = generate_exposure((), 2, 3, 2, False,
                                  maximum_clause_size=1)
        self.assertTrue(roots)
        self.assertTrue(all(not is_tail(literal)
                            for formula in roots for clause in formula
                            for literal in clause))

        node = {
            "rule": "expose_at_clause",
            "formula": [[2, {"tail": 9, "kind": "any"}]],
            "clause": 0,
            "variable": 3,
            "degrees": [[3, 1, True]],
        }
        children = expected_children(node, maximum_clause_size=2)
        self.assertTrue(children)
        self.assertTrue(all(
            len({abs(literal) for literal in clause if type(literal) is int}) <= 2
            for formula in children for clause in formula))

    def test_bounded_checker_rejects_width_increasing_semantic_step(self):
        tail1 = {"tail": 7, "kind": "any"}
        tail2 = {"tail": 8, "kind": "any"}
        parent = [[2, 3, tail1], [-2, 4, tail2]]
        child = [[3, 4, tail1, tail2]]
        proof = {
            "kind": "decompose",
            "transition": "semantic",
            "formula": parent,
            "alternatives": [{
                "offset": 1,
                "decrease": 1,
                "formula": child,
                "proof": call(child),
            }],
        }
        with self.assertRaisesRegex(VerificationError, "width upper bound 4"):
            self.check_data(bounded_certificate(proof, 3))

    def test_bounded_checker_keeps_original_tail_bound(self):
        tail = {"tail": 7, "kind": "any"}
        parent = [[2, tail]]
        child = [[2, 3, tail]]
        proof = {
            "kind": "decompose",
            "transition": "semantic",
            "formula": parent,
            "alternatives": [{
                "offset": 0,
                "decrease": 0,
                "formula": child,
                "proof": call(child),
            }],
        }
        with self.assertRaisesRegex(VerificationError, "width upper bound 4"):
            self.check_data(bounded_certificate(proof, 3))

    def test_repeated_tail_uses_smallest_source_bound(self):
        from verifier.formula import derive_tail_bounds
        tail = {"tail": 7, "kind": "any"}
        self.assertEqual(
            derive_tail_bounds([[2, tail], [3, 4, tail]], 3),
            {7: 1})

    def test_bounded_checker_rejects_unknown_tail(self):
        tail1 = {"tail": 7, "kind": "any"}
        tail2 = {"tail": 8, "kind": "any"}
        parent = [[2, tail1]]
        child = [[2, tail2]]
        proof = {
            "kind": "decompose",
            "transition": "semantic",
            "formula": parent,
            "alternatives": [{
                "offset": 0,
                "decrease": 0,
                "formula": child,
                "proof": call(child),
            }],
        }
        with self.assertRaisesRegex(VerificationError, "unrelated tail"):
            self.check_data(bounded_certificate(proof, 3))

    def test_old_certificate_has_unrestricted_meaning(self):
        proof = {
            "kind": "decompose",
            "transition": "semantic",
            "formula": [[2, 3, 4, 5]],
            "alternatives": [{
                "offset": 1,
                "decrease": 1,
                "formula": [],
                "proof": call([]),
            }],
        }
        self.check_data(certificate(proof))
        invalid = certificate(proof)
        invalid["maximum_clause_size"] = 3
        with self.assertRaisesRegex(VerificationError, "top-level fields"):
            self.check_data(invalid)


if __name__ == "__main__":
    unittest.main()
