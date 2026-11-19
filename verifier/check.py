import json
from collections import Counter
from fractions import Fraction

import numpy as np

from .formula import assignment_residual, canonical_formula, parse_formula, tail_ids
from .refine import POSSIBLE_DEGREES, expected_children
from .semantic import optimum_vector


class VerificationError(Exception):
    pass


class _Checker:
    def __init__(self, target, *, bottleneck):
        self.target = target
        self.inverse_target = 1 / target
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

    def _read_formula(self, node, path):
        if not isinstance(node, dict):
            self.fail(path, "node must be an object")
        return parse_formula(node.get("formula"))

    def check(self, proof):
        if self.bottleneck and self.target != Fraction(1609, 1250):
            self.fail("target", "bottleneck target must be 1.2872")

        formula = self._read_formula(proof, "proof")
        if self.bottleneck:
            root = [[2, {"tail": i, "kind": "any"}] for i in range(3)]
            root += [[-2, {"tail": i, "kind": "any"}] for i in range(3, 5)]
            if canonical_formula(formula) != canonical_formula(parse_formula(root)):
                self.fail(
                    "proof", "bottleneck root must be the (3,2) family with five arbitrary tails"
                )

        self._coverage(proof, formula, "proof", 1)

    def _coverage(self, node, formula, path, depth):
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)

        kind = node.get("kind")
        if kind == "strategy":
            if set(node) != {"kind", "formula", "proof"}:
                self.fail(path, "invalid strategy fields")

            proof = node["proof"]
            proof_path = path + ".proof"
            proof_formula = self._read_formula(proof, proof_path)
            if Counter(formula) != Counter(proof_formula):
                self.fail(path, "strategy formula differs from its proof formula")

            vector = self._strategy(proof, proof_formula, proof_path, depth + 1)
            if not vector or min(vector) <= 0:
                self.fail(path, f"all decreases must be positive integers: {vector}")

            weight = sum(self.inverse_target ** decrease for decrease in vector)
            if weight > 1:
                self.fail(path, f"branching vector {vector} violates the target")

            self.strategies += 1
            return

        if kind != "refine":
            self.fail(path, f"expected refine or strategy, got {kind!r}")

        rule = node.get("rule")
        fields = {"kind", "formula", "rule", "clause", "children"}
        if rule == "expose_at_clause":
            fields.update(("variable", "degrees"))
        if set(node) != fields:
            self.fail(path, "invalid refine fields")

        if self.bottleneck and rule == "expose_at_clause":
            degrees = node["degrees"]
            if (not isinstance(degrees, list) or
                    sorted(degrees) != sorted(map(list, POSSIBLE_DEGREES))):
                self.fail(path, "bottleneck exposure must cover the five baseline degree classes")

        children = node["children"]
        if not isinstance(children, list) or not children:
            self.fail(path, "refine must have nonempty children")

        try:
            expected = {canonical_formula(child) for child in expected_children(node, formula)}
            parsed_children = []
            for index, child in enumerate(children):
                child_path = f"{path}.children[{index}]"
                child_formula = self._read_formula(child, child_path)
                parsed_children.append((child, child_formula, child_path))

            actual = {canonical_formula(child_formula)
                      for _, child_formula, _ in parsed_children}
        except (KeyError, TypeError, ValueError) as error:
            self.fail(path, str(error))

        if actual != expected:
            self.fail(path, f"refine coverage mismatch: expected {len(expected)}, got {len(actual)}")
        if len(actual) != len(children):
            self.fail(path, "duplicate child formula")

        for child, child_formula, child_path in parsed_children:
            self._coverage(child, child_formula, child_path, depth + 1)

    def _strategy(self, node, formula, path, depth):
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)

        kind = node.get("kind")
        if kind == "call":
            if set(node) != {"kind", "formula"}:
                self.fail(path, "invalid call fields")
            return [0]

        if kind == "assumption":
            if set(node) != {"kind", "formula", "name", "vector"}:
                self.fail(path, "invalid assumption fields")
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
            branch_weight = sum(self.inverse_target ** decrease for decrease in vector)
            return [1] if self.inverse_target > branch_weight else vector

        if kind != "decompose":
            self.fail(path, f"expected decompose or call, got {kind!r}")
        alternatives = node.get("alternatives")
        if not isinstance(alternatives, list) or not alternatives:
            self.fail(path, "decompose has no constructive alternatives")

        transition = node.get("transition")
        fields = {"kind", "formula", "transition", "alternatives"}
        if transition == "assign":
            fields.add("variable")
        if set(node) != fields:
            self.fail(path, "invalid decomposition fields")

        child_formulas = []
        for index, alternative in enumerate(alternatives):
            if (not isinstance(alternative, dict) or
                    set(alternative) != {"offset", "decrease", "formula", "proof"}):
                self.fail(path, f"invalid fields in alternative {index}")
            if type(alternative["decrease"]) is not int:
                self.fail(path, f"decrease in alternative {index} must be an integer")
            child_formulas.append(parse_formula(alternative["formula"]))

        if transition == "assign":
            if len(alternatives) != 2 or type(node["variable"]) is not int:
                self.fail(path, "assign needs a variable and exactly two alternatives")

            for index, value in enumerate((True, False)):
                expected_formula, expected_offset, expected_decrease = assignment_residual(
                    formula, node["variable"], value
                )
                alternative = alternatives[index]
                if (Counter(child_formulas[index]) != Counter(expected_formula) or
                        type(alternative["offset"]) is not int or
                        alternative["offset"] != expected_offset or
                        alternative["decrease"] != expected_decrease):
                    self.fail(path, f"assignment alternative {index} is incorrect")

        elif transition == "semantic":
            try:
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
                if alternative["decrease"] != expected:
                    self.fail(path, "semantic alternative has incorrect decrease")
        else:
            self.fail(path, f"unknown transition {transition!r}")

        vector = []
        for index, (alternative, child_formula) in enumerate(zip(alternatives, child_formulas)):
            proof = alternative["proof"]
            proof_path = f"{path}.alternatives[{index}].proof"
            proof_formula = self._read_formula(proof, proof_path)
            if Counter(child_formula) != Counter(proof_formula):
                self.fail(path, f"alternative {index} formula differs from child proof")

            local_decrease = alternative["decrease"]
            child_vector = self._strategy(proof, proof_formula, proof_path, depth + 1)
            vector.extend(local_decrease + value for value in child_vector)

        return vector


def load_and_check(filename, *, bottleneck=False):
    """Check a JSON certificate and return its verification statistics and assumptions."""
    with open(filename, "r", encoding="utf-8") as stream:
        certificate = json.load(stream)

    if not isinstance(certificate, dict) or set(certificate) != {"format", "target", "proof"}:
        raise VerificationError("top-level fields are invalid")
    if certificate["format"] != "maxsat-local-proof-v2":
        raise VerificationError("unknown certificate format")

    target = certificate["target"]
    if not isinstance(target, dict) or set(target) != {"numerator", "denominator"}:
        raise VerificationError("invalid target")
    numerator, denominator = target["numerator"], target["denominator"]
    if (type(numerator) is not int or type(denominator) is not int or
            numerator <= denominator or denominator <= 0):
        raise ValueError("target must be a rational number greater than one")

    checker = _Checker(Fraction(numerator, denominator), bottleneck=bottleneck)
    checker.check(certificate["proof"])
    return checker
