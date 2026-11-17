"""Proof-backed lemma instantiation, context transfer and certificate checks."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from lemma_library import (PROOF_FILES, expand_lemma_applications,
                           save_session_lemma, validate_saved_lemma)
from verifier.check import Checker, VerificationError, load_and_check
from verifier.arithmetic import vector_weight
from verifier.formula import assignment_residual, normalize_formula, is_tail
from verifier.refine import expected_children


def json_formula(formula):
    return [[{"tail": lit[1], "kind": lit[2]} if is_tail(lit) else lit
             for lit in clause] for clause in formula]


def assign_proof(formula, variable):
    alternatives = []
    for value in (True, False):
        child, offset, decrease = assignment_residual(normalize_formula(formula), variable, value)
        child = json_formula(child)
        alternatives.append({"offset": offset, "decrease": decrease, "formula": child,
                             "proof": {"kind": "call", "formula": child}})
    return {"kind": "decompose", "transition": "assign", "variable": variable,
            "formula": formula, "alternatives": alternatives}


def tail_case_proof():
    root = {"kind": "refine", "rule": "tail_empty_or_nonempty", "clause": 0,
            "formula": [[2, {"tail": 0, "kind": "any"}]]}
    root["children"] = [assign_proof(json_formula(child), 2)
                        for child in sorted(expected_children(root), key=repr)]
    return root


def application():
    tail = lambda idx, kind="any": {"tail": idx, "kind": kind}
    return {"kind": "lemma", "name": "step5.1", "roles": [7],
            "witness_clauses": [3], "vector": [4, 2],
            "formula": [[7, 3, tail(11)], [7, -3, tail(11)],
                        [7, tail(12, "nonempty")], [-7], [-7, 4, tail(13)],
                        [3, 4, tail(14)], [-3, -4, tail(15)]]}


class LemmaTests(unittest.TestCase):
    def check(self, proof, numerator=12872, denominator=10000):
        data = {"format": "maxsat-local-proof-v2",
                "target": {"numerator": numerator, "denominator": denominator},
                "proof": {"kind": "strategy", "formula": proof["formula"], "proof": proof}}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "proof.json"
            path.write_text(json.dumps(data))
            return load_and_check(path)

    def test_definition_is_constructive(self):
        definition = json.loads(PROOF_FILES["step5.1"].read_text())
        checker = self.check(definition["proof"])
        self.assertEqual(checker.assumptions, [])
        self.assertEqual(Checker(12872, 10000)._strategy(definition["proof"], "proof", 1), [4, 2])

    def test_context_and_correlated_tails_have_zero_cost(self):
        source = application()
        saved = deepcopy(source)
        proof = expand_lemma_applications(source)
        self.assertEqual(source, saved)
        self.assertEqual(len(proof["formula"]), 7)
        self.assertEqual(len(proof["proof"]["formula"]), 5)
        self.assertEqual(proof["kept_variables"], [7])
        self.assertEqual(set(proof["clause_map"]), set(range(5)))
        self.assertEqual(Checker(12872, 10000)._strategy(proof, "proof", 1), [4, 2])
        self.assertEqual(self.check(proof).assumptions, [])

    def test_negative_role_renames_and_reorders_assignment_branches(self):
        source = application()
        source["roles"] = [-7]
        source["formula"] = [[-lit if type(lit) is int and abs(lit) == 7 else lit
                              for lit in clause] for clause in source["formula"]]
        proof = expand_lemma_applications(source)
        self.assertEqual(proof["proof"]["variable"], 7)
        self.assertEqual(Checker(12872, 10000)._strategy(proof, "proof", 1), [2, 4])
        self.assertEqual(self.check(proof).assumptions, [])

    def test_q_is_checked_after_splicing_in_a_branch(self):
        lemma = expand_lemma_applications(application())
        # (4,2) fails at q=6/5. The enclosing branch contributes a decrease
        # of five on each side, giving (9,7,5), which passes at this same q.
        with self.assertRaises(VerificationError):
            self.check(lemma, 6, 5)
        formula = lemma["formula"]
        parent = {"kind": "decompose", "transition": "assign", "variable": 9,
                  "formula": formula + [[9]] * 5,
                  "alternatives": [
                      {"offset": 5, "decrease": 5, "formula": formula, "proof": lemma},
                      {"offset": 0, "decrease": 5, "formula": formula,
                       "proof": {"kind": "call", "formula": formula}}]}
        self.assertEqual(Checker(6, 5)._strategy(parent, "proof", 1), [9, 7, 5])
        self.assertEqual(self.check(parent, 6, 5).assumptions, [])

    def test_empty_binding_and_nonempty_weakening(self):
        source = application()
        source["formula"][2] = [7]
        proof = expand_lemma_applications(source)
        self.assertTrue(any(binding["literals"] == [] for binding in proof["tail_bindings"]))
        self.check(proof)
        # A forgotten displayed literal is a witness for a nonempty tail.
        proof["proof"]["formula"][0][-1]["kind"] = "nonempty"
        self.check(proof)
        # An empty disjunction cannot meet that same structural requirement.
        proof["proof"]["formula"][2][-1]["kind"] = "nonempty"
        with self.assertRaisesRegex(VerificationError, "nonempty witness"):
            self.check(proof)

    def test_forged_context_and_fake_decrease_are_rejected(self):
        original = expand_lemma_applications(application())
        bad = deepcopy(original)
        bad["tail_bindings"][0]["literals"].append(999)
        with self.assertRaisesRegex(VerificationError, "reconstruct"):
            self.check(bad)
        bad = deepcopy(original)
        bad["tail_bindings"][0]["literals"].append(7)
        with self.assertRaisesRegex(VerificationError, "kept variable"):
            self.check(bad)
        bad = deepcopy(original)
        bad["decrease"] = 2  # two clauses merely moved into external context
        with self.assertRaisesRegex(VerificationError, "fields"):
            self.check(bad)
        bad = deepcopy(original)
        bad["clause_map"][1] = bad["clause_map"][0]
        with self.assertRaisesRegex(VerificationError, "clause map"):
            self.check(bad)
        bad = deepcopy(original)
        bad["proof"]["formula"].pop()
        bad["clause_map"].pop()
        with self.assertRaisesRegex(VerificationError, "every incident clause"):
            self.check(bad)

    def test_proof_cannot_capture_forgotten_variables(self):
        proof = expand_lemma_applications(application())
        proof["proof"]["alternatives"][0]["proof"]["formula"] = [[3]]
        with self.assertRaisesRegex(VerificationError, "captures a forgotten variable"):
            self.check(proof)

    def test_invalid_matches_and_unexpanded_leaves_are_rejected(self):
        for mutation in (lambda a: a["roles"].__setitem__(0, -7),
                         lambda a: a["witness_clauses"].__setitem__(0, 0),
                         lambda a: a["vector"].__setitem__(0, 5),
                         lambda a: a["formula"].append([7])):
            bad = application()
            mutation(bad)
            with self.assertRaises(ValueError):
                expand_lemma_applications(bad)
        with self.assertRaises(ValueError):
            expand_lemma_applications(application(), {})
        with self.assertRaises(VerificationError):
            self.check(application())

    def test_legacy_step51_import_is_expanded(self):
        source = application()
        source.pop("roles")
        source.pop("witness_clauses")
        source["kind"] = "assumption"
        self.assertEqual(self.check(expand_lemma_applications(source)).assumptions, [])

    def test_cyclic_proof_dependency_is_rejected(self):
        definition = json.loads(PROOF_FILES["step5.1"].read_text())
        definition["proof"] = {"kind": "lemma", "name": "step5.1",
                               "formula": definition["proof"]["formula"],
                               "roles": [2], "witness_clauses": [3], "vector": [4, 2]}
        with self.assertRaisesRegex(ValueError, "cyclic"):
            expand_lemma_applications(application(), {"step5.1": definition})

    def test_refine_inside_decompose_checks_only_enclosing_target(self):
        refined = tail_case_proof()
        self.assertEqual(Checker(2, 1)._strategy(refined, "proof", 1), [1, 0])
        with self.assertRaises(VerificationError):
            self.check(refined, 2, 1)
        parent = assign_proof(refined["formula"] + [[9], [9]], 9)
        parent["alternatives"][0]["proof"] = refined
        self.assertEqual(Checker(2, 1)._strategy(parent, "proof", 1), [3, 2, 2])
        self.check(parent, 2, 1)

    def test_refine_uses_max_at_q_instead_of_sum_or_branching_factor(self):
        refined = tail_case_proof()
        for child, vector in zip(refined["children"], ([1, 8], [3, 3])):
            child.clear()
            child.update({"kind": "assumption", "name": "fixture", "vector": list(vector)})
        # Restore the two distinct case formulas after replacing the strategies.
        for child, formula in zip(refined["children"], sorted(expected_children(refined), key=repr)):
            child["formula"] = json_formula(formula)
        self.assertEqual(Checker(6, 5)._strategy(refined, "proof", 1), [3, 3])
        self.assertEqual(Checker(2, 1)._strategy(refined, "proof", 1), [1, 8])

    def test_nested_refine_rejects_missing_duplicate_and_forged_cases(self):
        for mutation in (lambda p: p["children"].pop(),
                         lambda p: p["children"].append(deepcopy(p["children"][0])),
                         lambda p: p["children"][0].__setitem__("formula", [[2], [2]])):
            bad = tail_case_proof()
            mutation(bad)
            with self.assertRaisesRegex(VerificationError, "coverage|duplicate"):
                Checker(2, 1)._strategy(bad, "proof", 1)

    def test_save_and_splice_refined_lemma_with_weight_above_one(self):
        target = {"numerator": 2, "denominator": 1}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.json"
            saved = save_session_lemma(tail_case_proof(), path, target)
            saved = json.loads(path.read_text())
        self.assertEqual(saved["vector"], [1, 0])
        self.assertGreater(vector_weight(saved["vector"], **target), 1)
        validate_saved_lemma(saved)
        leaf = {"kind": "lemma", "name": saved["id"], "roles": [-7],
                "witness_clauses": [], "vector": saved["vector"],
                "formula": [[-7, 3, {"tail": 11, "kind": "any"}], [3]]}
        attached = expand_lemma_applications(leaf, {saved["id"]: saved}, target=target)
        self.assertEqual(attached["proof"]["kind"], "refine")
        self.assertCountEqual(Checker(2, 1)._strategy(attached, "proof", 1), [0, 1])
        self.assertEqual(attached['role_bindings'][0]['literal'],-7)
        parent = assign_proof(leaf["formula"] + [[9], [9]], 9)
        parent["alternatives"][0]["proof"] = attached
        self.check(parent, 2, 1)
        with self.assertRaisesRegex(ValueError, "fixed target"):
            expand_lemma_applications(leaf, {saved["id"]: saved},
                                      target={"numerator": 3, "denominator": 1})
        with self.assertRaisesRegex(VerificationError, "target differs"):
            Checker(3, 1)._strategy(attached, "proof", 1)
        with self.assertRaisesRegex(ValueError, "fixed target"):
            expand_lemma_applications(leaf, {saved["id"]: saved})

    def test_saved_exposure_preserves_degree_premises_and_renames_fresh_variable(self):
        proof = {"kind": "refine", "rule": "expose_at_clause", "variable": 3,
                 "clause": 0, "degrees": [[1, 1, False]],
                 "formula": [[2, {"tail": 0, "kind": "nonempty"}], [-2]]}
        proof["children"] = [{"kind": "call", "formula": json_formula(child)}
                             for child in expected_children(proof)]
        target = {"numerator": 2, "denominator": 1}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expose.json"
            save_session_lemma(proof, path, target)
            definition = json.loads(path.read_text())
        self.assertEqual(definition["premises"]["degrees"][0]["degrees"], [[1, 1, False]])
        leaf = {"kind": "lemma", "name": definition["id"], "roles": [7],
                "witness_clauses": [1], "vector": [0],
                "formula": [[7, 3], [-7], [3]]}
        attached = expand_lemma_applications(leaf, {definition["id"]: definition}, target=target)
        self.assertGreater(attached["proof"]["variable"], 7)
        self.assertEqual(Checker(2, 1)._strategy(attached, "proof", 1), [0])

    def test_saved_metadata_is_checked_and_failed_export_preserves_file(self):
        target = {"numerator": 2, "denominator": 1}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.json"
            save_session_lemma(tail_case_proof(), path, target)
            definition = json.loads(path.read_text())
            for mutation in (lambda d: d.__setitem__("vector", [10]),
                             lambda d: d.__setitem__("premises", {})):
                bad = deepcopy(definition)
                mutation(bad)
                with self.assertRaises(ValueError):
                    validate_saved_lemma(bad)
            original = path.read_text()
            bad = tail_case_proof()
            bad["children"].pop()
            with self.assertRaises(VerificationError):
                save_session_lemma(bad, path, target)
            self.assertEqual(path.read_text(), original)

    def test_resaved_step51_context_is_renamed_with_its_tail_bindings(self):
        target = {"numerator": 12872, "denominator": 10000}
        source = application()
        source["formula"][1][-1]["tail"] = 16
        original = expand_lemma_applications(source)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "step.json"
            save_session_lemma(original, path, target)
            definition = json.loads(path.read_text())
        leaf = {"kind": "lemma", "name": definition["id"], "roles": [30, 31, 32],
                "witness_clauses": [], "vector": [4, 2],
                "formula": []}
        from lemma_library import _rename_proof
        renamed = _rename_proof(original, {3: 30, 4: 31, 7: 32}, 100)
        leaf["formula"] = renamed["formula"]
        attached = expand_lemma_applications(leaf, {definition["id"]: definition}, target=target)
        self.assertEqual(Checker(**target)._strategy(attached, "proof", 1), [4, 2])


if __name__ == "__main__":
    unittest.main()
