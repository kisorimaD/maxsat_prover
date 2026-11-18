import json

import numpy as np

from .arithmetic import check_vector, target_fraction
from .formula import (assignment_residual, canonical_formula,
                      normalize_formula, tail_ids)
from .refine import POSSIBLE_DEGREES, expected_children
from .semantic import optimum_vector


class VerificationError(Exception):
    pass


class Checker:
    def __init__(self, numerator, denominator, *, bottleneck=False):
        self.target = target_fraction(numerator, denominator)
        self.numerator = numerator
        self.denominator = denominator
        self.nodes = 0
        self.strategies = 0
        self.max_depth = 0
        self.assumptions = []
        self.bottleneck = bottleneck

    def fail(self, path, message):
        raise VerificationError(
            f"{path}: {message} "
            f"[checked_nodes={self.nodes}, strategies={self.strategies}, "
            f"depth={self.max_depth}]"
        )

    def check(self, proof):
        if not isinstance(proof, dict):
            self.fail("proof", "node must be an object")
        if self.bottleneck:
            if self.target != target_fraction(12872, 10000):
                self.fail("target", "bottleneck target must be 1.2872")
            root = [[2, {"tail": i, "kind": "any"}] for i in range(3)]
            root += [[-2, {"tail": i, "kind": "any"}] for i in range(3, 5)]
            if canonical_formula(proof.get("formula")) != canonical_formula(root):
                self.fail("proof", "bottleneck root must be the (3,2) family with five arbitrary tails")
        self._coverage(proof, "proof", 1)

    def _coverage(self, node, path, depth):
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)
        if not isinstance(node, dict):
            self.fail(path, "node must be an object")
        kind = node.get("kind")
        if kind == "strategy":
            if set(node) != {"kind", "formula", "proof"}:
                self.fail(path, "invalid strategy fields")
            wrapper_formula = normalize_formula(node["formula"])
            proof_formula = normalize_formula(node["proof"].get("formula"))
            if wrapper_formula != proof_formula:
                self.fail(path, "strategy formula differs from its proof formula")
            vector = self._strategy(node["proof"], path + ".proof", depth + 1)
            try:
                check_vector(vector, self.numerator, self.denominator)
            except ValueError as error:
                self.fail(path, str(error))
            self.strategies += 1
            return
        if kind != "refine":
            self.fail(path, f"expected refine or strategy, got {kind!r}")
        fields = {"kind", "formula", "rule", "clause", "children"}
        if node.get("rule") == "expose_at_clause":
            fields.update(("variable", "degrees"))
        if set(node) != fields:
            self.fail(path, "invalid refine fields")
        if self.bottleneck and node.get("rule") == "expose_at_clause":
            degrees = node["degrees"]
            if (not isinstance(degrees, list) or
                    sorted(degrees) != sorted(map(list, POSSIBLE_DEGREES))):
                self.fail(path, "bottleneck exposure must cover the five baseline degree classes")
        children = node.get("children")
        if not isinstance(children, list) or not children:
            self.fail(path, "refine must have nonempty children")
        try:
            expected = {canonical_formula(formula)
                        for formula in expected_children(node)}
            actual = {canonical_formula(child["formula"]) for child in children}
        except (KeyError, TypeError, ValueError) as error:
            self.fail(path, str(error))
        if actual != expected:
            self.fail(path, f"refine coverage mismatch: expected {len(expected)}, got {len(actual)}")
        if len(actual) != len(children):
            self.fail(path, "duplicate child formula")
        for index, child in enumerate(children):
            self._coverage(child, f"{path}.children[{index}]", depth + 1)

    def _strategy(self, node, path, depth):
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)
        if not isinstance(node, dict):
            self.fail(path, "strategy node must be an object")
        kind = node.get("kind")
        if kind == "call":
            if set(node) != {"kind", "formula"}:
                self.fail(path, "invalid call fields")
            normalize_formula(node["formula"])
            return [0]
        if kind == "assumption":
            if set(node) != {"kind", "formula", "name", "vector"}:
                self.fail(path, "invalid assumption fields")
            formula = normalize_formula(node["formula"])
            vector = node["vector"]
            if (not isinstance(node["name"], str) or not node["name"] or
                    not isinstance(vector, list) or not vector or
                    any(type(value) is not int or value <= 0 for value in vector)):
                self.fail(path, "invalid trusted assumption")
            if node["name"] not in {"lemma2", "lemma3", "lemma4", "double_lemma3"}:
                self.fail(path, f"unknown imported lemma {node['name']!r}")
            self.assumptions.append({"path": path, "name": node["name"],
                                     "formula": node["formula"], "vector": vector})
            # The imported vector covers the branching case. For double_lemma3
            # it also dominates (8,2), the case of a reduction at the second step.
            inverse = 1 / self.target
            branch_weight = sum(inverse ** decrease for decrease in vector)
            return [1] if inverse > branch_weight else vector
        if kind != "decompose":
            self.fail(path, f"expected decompose or call, got {kind!r}")
        formula = normalize_formula(node.get("formula"))
        alternatives = node.get("alternatives")
        if not isinstance(alternatives, list) or not alternatives:
            self.fail(path, "decompose has no constructive alternatives")

        transition = node.get("transition")
        fields = {"kind", "formula", "transition", "alternatives"}
        if transition == "assign":
            fields.add("variable")
        if set(node) != fields:
            self.fail(path, "invalid decomposition fields")
        if transition == "assign":
            if len(alternatives) != 2 or type(node.get("variable")) is not int:
                self.fail(path, "assign needs a variable and exactly two alternatives")
            for index, value in enumerate((True, False)):
                expected_formula, expected_offset, expected_decrease = \
                    assignment_residual(formula, node["variable"], value)
                actual_formula = normalize_formula(alternatives[index].get("formula"))
                if (actual_formula != expected_formula or
                        alternatives[index].get("offset") != expected_offset or
                        alternatives[index].get("decrease") != expected_decrease):
                    self.fail(path, f"assignment alternative {index} is incorrect")
        elif transition == "semantic":
            try:
                child_formulas = [normalize_formula(alternative["formula"])
                                  for alternative in alternatives]
                parent_tails = set(tail_ids(formula))
                if any(not set(tail_ids(child)).issubset(parent_tails)
                       for child in child_formulas):
                    raise ValueError("semantic child introduces an unrelated tail")
                boundary_ids = sorted(parent_tails)
                for alternative in alternatives:
                    offset = alternative.get("offset")
                    if offset != "infer" and (type(offset) is not int or
                                               not 0 <= offset <= len(formula)):
                        raise ValueError("offset must be an integer between zero and parent size")
                parent_values = optimum_vector(formula, boundary_ids).astype(np.int32)
                child_values = [optimum_vector(child, boundary_ids).astype(np.int32)
                                for child in child_formulas]
                if any(alternative["offset"] == "infer"
                       for alternative in alternatives):
                    if len(alternatives) != 1:
                        raise ValueError("inferred offset needs one semantic child")
                    differences = parent_values - child_values[0]
                    if differences.min() < 0 or differences.min() != differences.max():
                        raise ValueError("semantic reduction has no constant nonnegative offset")
                else:
                    shifted = [values + alternative["offset"]
                               for values, alternative in zip(child_values, alternatives)]
                    child_maximum = shifted[0]
                    for values in shifted[1:]:
                        child_maximum = np.maximum(child_maximum, values)
                    mismatches = (parent_values != child_maximum).nonzero()[0]
                    if len(mismatches):
                        raise ValueError(
                            f"OPT identity fails for boundary mask {int(mismatches[0])}")
            except (KeyError, TypeError, ValueError) as error:
                self.fail(path, str(error))
            for alternative, child in zip(alternatives, child_formulas):
                expected = len(formula) - len(child)
                if alternative.get("decrease") != expected:
                    self.fail(path, "semantic alternative has incorrect decrease")
        else:
            self.fail(path, f"unknown transition {transition!r}")

        vector = []
        for index, alternative in enumerate(alternatives):
            if set(alternative) != {"offset", "decrease", "formula", "proof"}:
                self.fail(path, f"invalid fields in alternative {index}")
            child_formula = normalize_formula(alternative["formula"])
            proof_formula = normalize_formula(alternative["proof"].get("formula"))
            if child_formula != proof_formula:
                self.fail(path, f"alternative {index} formula differs from child proof")
            local_decrease = alternative["decrease"]
            child_vector = self._strategy(alternative["proof"],
                                          f"{path}.alternatives[{index}].proof",
                                          depth + 1)
            vector.extend(local_decrease + value for value in child_vector)
        return vector


def load_and_check(filename, *, bottleneck=False):
    with open(filename, "r", encoding="utf-8") as stream:
        certificate = json.load(stream)
    if set(certificate) != {"format", "target", "proof"}:
        raise VerificationError("top-level fields are invalid")
    if certificate["format"] != "maxsat-local-proof-v2":
        raise VerificationError("unknown certificate format")
    target = certificate["target"]
    if set(target) != {"numerator", "denominator"}:
        raise VerificationError("invalid target")
    checker = Checker(target["numerator"], target["denominator"], bottleneck=bottleneck)
    checker.check(certificate["proof"])
    return checker
