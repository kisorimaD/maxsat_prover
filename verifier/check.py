import json

import numpy as np

from .arithmetic import check_vector, target_fraction, vector_weight
from .formula import (assignment_residual, canonical_formula,
                      normalize_formula, tail_ids)
from .refine import expected_children
from .semantic import optimum_vector
from .context import validate_local_context, validate_property_contexts
from .typed_tails import read_exclusions, canonical_state, expected_states, retained_exclusions


class VerificationError(Exception):
    pass


class Checker:
    def __init__(self, numerator, denominator, legacy=False, allow_restarts=False):
        target_fraction(numerator, denominator)
        self.numerator = numerator
        self.denominator = denominator
        self.nodes = 0
        self.strategies = 0
        self.max_depth = 0
        self.assumptions = []
        self.legacy = legacy
        self.degree_premises = []
        self.allow_restarts = allow_restarts
        self.restart_obligations = []

    def fail(self, path, message):
        raise VerificationError(
            f"{path}: {message} "
            f"[checked_nodes={self.nodes}, strategies={self.strategies}, "
            f"depth={self.max_depth}]"
        )

    def check(self, proof):
        try: validate_property_contexts(proof)
        except (KeyError,TypeError,ValueError) as error:self.fail('proof',str(error))
        self._coverage(proof, "proof", 1)

    def _coverage(self, node, path, depth, exclusions=None):
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)
        if not isinstance(node, dict):
            self.fail(path, "node must be an object")
        node, exclusions = self._typed_state(node, path, exclusions)
        kind = node.get("kind")
        if kind == "strategy":
            if set(node) != {"kind", "formula", "proof"}:
                self.fail(path, "invalid strategy fields")
            wrapper_formula = normalize_formula(node["formula"])
            proof_formula = normalize_formula(node["proof"].get("formula"))
            if wrapper_formula != proof_formula:
                self.fail(path, "strategy formula differs from its proof formula")
            vector = self._strategy(node["proof"], path + ".proof", depth + 1,
                                    premise_exclusions=exclusions)
            try:
                self.check_strategy_result(node["proof"], vector)
            except ValueError as error:
                self.fail(path, str(error))
            self.strategies += 1
            return
        if kind != "refine":
            self.fail(path, f"expected refine or strategy, got {kind!r}")
        children = self._refine_children(node, path, exclusions)
        for index, (child, child_exclusions) in enumerate(children):
            self._coverage(child, f"{path}.children[{index}]", depth + 1, child_exclusions)

    def _typed_state(self, node, path, expected):
        if 'tail_exclusions' not in node and not expected:
            return node, {}
        try:
            actual = read_exclusions(node)
            if actual != (expected or {}):
                raise ValueError('tail exclusions differ from the enclosing structural case')
        except (KeyError, TypeError, ValueError) as error:
            self.fail(path, str(error))
        clean = dict(node)
        clean.pop('tail_exclusions', None)
        return clean, actual

    def _refine_children(self, node, path, exclusions=None):
        fields = {"kind", "rule", "formula", "clause", "children"}
        if node.get("rule") in ("expose_at_clause", "expose_type_at_clause"):
            fields.add("variable")
            if "degrees" in node:
                fields.add("degrees")
            if node.get("rule") == "expose_type_at_clause": fields.add("degree")
        if set(node) != fields:
            self.fail(path, "invalid refine fields")
        children = node.get("children")
        if not isinstance(children, list) or not children:
            self.fail(path, "refine must have nonempty children")
        try:
            expected = {canonical_state(formula, state) for formula, state in
                        expected_states(node, exclusions or {}, legacy=self.legacy)}
            actual = {canonical_state(child["formula"], read_exclusions(child)) for child in children}
        except (KeyError, TypeError, ValueError) as error:
            self.fail(path, str(error))
        if actual != expected:
            self.fail(path, f"refine coverage mismatch: expected {len(expected)}, got {len(actual)}")
        if len(actual) != len(children):
            self.fail(path, "duplicate child formula")
        if node.get("rule") in ("expose_at_clause", "expose_type_at_clause"):
            from .refine import POSSIBLE_DEGREES, LEGACY_DEGREES
            self.degree_premises.append({
                "path": path,
                "degrees": node.get("degrees", LEGACY_DEGREES if self.legacy
                                    else POSSIBLE_DEGREES),
            })
        return [(child, read_exclusions(child)) for child in children]

    def check_strategy_result(self, proof, vector):
        from .restart import progressing
        if not progressing(proof):
            raise ValueError('unpaid call without clause decrease or a checked restart')
        if self.allow_restarts:
            if any(type(d) is not int or d<0 for d in vector) or vector_weight(vector,self.numerator,self.denominator)>1:
                raise ValueError('inductive strategy violates the target')
        else:check_vector(vector,self.numerator,self.denominator)

    def _strategy(self, node, path, depth, exclusions=None, premise_exclusions=None):
        if depth == 1:
            try: validate_property_contexts(node)
            except (KeyError,TypeError,ValueError) as error:self.fail(path,str(error))
        self.nodes += 1
        self.max_depth = max(self.max_depth, depth)
        if not isinstance(node, dict):
            self.fail(path, "strategy node must be an object")
        node, exclusions = self._typed_state(node, path, exclusions)
        knowledge = dict(premise_exclusions or {})
        for tail, types in exclusions.items():
            knowledge[tail] = frozenset(set(knowledge.get(tail, ())) | set(types))
        kind = node.get("kind")
        if kind == "strategy":
            if set(node) != {"kind", "formula", "proof"}:
                self.fail(path, "invalid strategy fields")
            if normalize_formula(node["formula"]) != normalize_formula(node["proof"].get("formula")):
                self.fail(path, "strategy formula differs from its proof formula")
            # A saved session contains strategy wrappers beneath refinements.
            # Only the enclosing strategy checks the target.
            return self._strategy(node["proof"], path + ".proof", depth + 1,
                                  premise_exclusions=knowledge)
        if kind == "refine":
            children = self._refine_children(node, path, exclusions)
            vectors = [self._strategy(child, f"{path}.children[{index}]", depth + 1, child_exclusions,
                                     premise_exclusions=retained_exclusions(normalize_formula(child['formula']), knowledge))
                       for index, (child, child_exclusions) in enumerate(children)]
            # Structural cases describe one instance, not recursive calls.
            # At fixed q the worst vector is an upper bound for every case.
            return max(vectors, key=lambda vector: vector_weight(
                vector, self.numerator, self.denominator))
        if kind == "local_context":
            try:
                validate_local_context(node)
                if "target" in node:
                    target = node["target"]
                    if (not isinstance(target, dict) or
                            set(target) != {"numerator", "denominator"} or
                            target_fraction(target["numerator"], target["denominator"]) !=
                            target_fraction(self.numerator, self.denominator)):
                        raise ValueError("lemma target differs from the certificate target")
            except (KeyError, TypeError, ValueError) as error:
                self.fail(path, str(error))
            # The target is checked only for the complete enclosing strategy.
            first_premise = len(self.degree_premises)
            vector = self._strategy(node["proof"], path + ".proof", depth + 1)
            if "degree_scope" in node:
                from .refine import checked_degree_scope, degree_is_covered
                scope = checked_degree_scope(node["degree_scope"])
                for premise in self.degree_premises[first_premise:]:
                    if any(not degree_is_covered(degree, premise["degrees"]) for degree in scope):
                        self.fail(path, "lemma proof does not cover the application degree scope")
                self.degree_premises.append({"path": path + ".degree_scope", "degrees": scope})
            return vector
        if kind == "restart":
            if not self.allow_restarts:self.fail(path,'restart requires the local-induction contract (--allow-restarts)')
            from .restart import validate_restart
            try:eliminated=validate_restart(node)
            except (KeyError,TypeError,ValueError) as error:self.fail(path,str(error))
            self.restart_obligations.append({'path':path,'rule':node['rule'],'eliminated_variables':eliminated,
                                             'continuation':'complete global solver, reclassify from the beginning'})
            return [0]
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
            self.assumptions.append({"path": path, "name": node["name"],
                                     "formula": node["formula"], "vector": vector})
            return vector
        if kind == "xiao_property1_branch":
            from .property2 import property1_sides, property2_sides
            if set(node) != {'kind','formula','variable','properties','degrees','children'}:
                self.fail(path, 'invalid Property 1 fields')
            properties, children = node['properties'], node['children']
            if (not isinstance(properties,list) or len(properties)!=2 or 1 not in properties or
                    any(type(p) is not int or p not in (0,1,2) for p in properties) or
                    not isinstance(children,list) or len(children)!=2):
                self.fail(path, 'Property 1 needs two branch sides')
            try:
                formula = normalize_formula(node['formula'])
                eligible1 = property1_sides(formula,node['variable'],knowledge,node['degrees'])
                eligible2 = property2_sides(formula,node['variable'])
            except (KeyError,TypeError,ValueError) as error:
                self.fail(path,str(error))
            result=[]
            for side, (prop,child) in enumerate(zip(properties,children)):
                residual,_,decrease=assignment_residual(formula,node['variable'],side==0)
                if not isinstance(child,dict) or normalize_formula(child.get('formula'))!=residual:
                    self.fail(path,'incorrect Property 1 assignment residual')
                if prop:
                    if not (eligible1 if prop==1 else eligible2)[side]:
                        self.fail(path,'Property 1/2 side does not meet its structural conditions')
                    if child!={'kind':'call','formula':child['formula']}:
                        self.fail(path,'imported property side must be an opaque call')
                    vector=([18,11,11,4] if prop==1 else max(([11,3],[11,10,4]),
                        key=lambda v:vector_weight(v,self.numerator,self.denominator)))
                    self.assumptions.append({
                        'path':path+f'.children[{side}]','name':f'xiao_property{prop}',
                        'formula':node['formula'],'variable':node['variable'], 'value':side==0,
                        'vector':vector,'vector_origin':'before_assignment',
                        'premises':['globally reduced by Xiao R-Rules 1-9',
                                    'all variables are in the recorded Step 6 family',
                                    'Step 4 inapplicable: no unit (2,2) clauses, including hidden tails']})
                    self.degree_premises.append({'path':path,'degrees':node['degrees']})
                    result.extend(vector)
                else:
                    vector=self._strategy(child,f'{path}.children[{side}]',depth+1)
                    result.extend(decrease+d for d in vector)
            return result
        if kind == "xiao_property2_branch":
            from .property2 import property2_sides, STEP6_DEGREES
            if set(node) != {"kind", "formula", "variable", "imported_sides", "children"}:
                self.fail(path, "invalid Property 2 fields")
            sides, children = node["imported_sides"], node["children"]
            if (not isinstance(sides, list) or len(sides) != 2 or
                    any(type(v) is not bool for v in sides) or not any(sides) or
                    not isinstance(children, list) or len(children) != 2):
                self.fail(path, "Property 2 needs two branch sides")
            try:
                formula = normalize_formula(node["formula"])
                eligible = property2_sides(formula, node["variable"])
            except (TypeError, ValueError) as error:
                self.fail(path, str(error))
            imported_vector = max(([11, 3], [11, 10, 4]), key=lambda v: vector_weight(
                v, self.numerator, self.denominator))
            result = []
            for index, child in enumerate(children):
                residual, _, decrease = assignment_residual(formula, node["variable"], index == 0)
                if not isinstance(child, dict) or normalize_formula(child.get("formula")) != residual:
                    self.fail(path, "incorrect Property 2 assignment residual")
                if sides[index]:
                    if not eligible[index]:
                        self.fail(path, "Property 2 side has no (2,2) witness")
                    if child != {"kind": "call", "formula": child["formula"]}:
                        self.fail(path, "imported Property 2 side must be an opaque call")
                    self.assumptions.append({
                        "path": path + f".children[{index}]", "name": "xiao_property2",
                        "formula": node["formula"], "variable": node["variable"],
                        "value": index == 0, "vector": imported_vector,
                        "vector_origin": "before_assignment",
                        "alternatives": [[11, 3], [11, 10, 4]],
                        "premises": ["globally reduced by Xiao R-Rules 1-9",
                                     "all variables are Step 6 (2,2), (3,1)-S, (4,1)-S",
                                     "Step 4 inapplicable: no unit (2,2) clauses, including hidden tails"]})
                    self.degree_premises.append({"path": path, "degrees": STEP6_DEGREES})
                    result.extend(imported_vector)
                else:
                    vector = self._strategy(child, f"{path}.children[{index}]", depth + 1)
                    result.extend(decrease + d for d in vector)
            return result
        if kind == "local_resolution":
            from .local_resolution import resolution_result
            if set(node) != {"kind", "formula", "variable", "rule", "proof"}:
                self.fail(path, "invalid local-resolution fields")
            try:
                residual, decrease = resolution_result(node["formula"], node["variable"], node["rule"])
                if not isinstance(node["proof"], dict) or normalize_formula(node["proof"].get("formula")) != residual:
                    raise ValueError("incorrect local-resolution residual")
            except (TypeError, ValueError) as error:
                self.fail(path, str(error))
            vector = self._strategy(node["proof"], path + ".proof", depth + 1)
            return [decrease+d for d in vector]
        if kind == "lemma3_split":
            if set(node) != {"kind", "formula", "variable", "long_decrease", "proof"}:
                self.fail(path, "invalid lemma3_split fields")
            from .lemma3 import resolution_alternative
            try:
                residual, bound = resolution_alternative(node["formula"], node["variable"])
                if type(node["long_decrease"]) is not int or node["long_decrease"] != bound:
                    raise ValueError("incorrect lemma3 long decrease")
                if normalize_formula(node["proof"].get("formula")) != residual:
                    raise ValueError("incorrect lemma3 resolution residual")
            except (KeyError, TypeError, ValueError) as error:
                self.fail(path, str(error))
            self.assumptions.append({"path": path, "name": "lemma3_split",
                                     "formula": node["formula"], "vector": [1, bound],
                                     "statement": "reduction_or_resolution_branch"})
            child = self._strategy(node["proof"], path + ".proof", depth + 1)
            branch = [bound] + [1 + d for d in child]
            # The theorem also permits an unspecified >=1 reduction. It
            # does not promise that this reduction preserves the continuation.
            return max(([1], branch), key=lambda v: vector_weight(
                v, self.numerator, self.denominator))
        if kind != "decompose":
            self.fail(path, f"expected decompose or call, got {kind!r}")
        formula = normalize_formula(node.get("formula"))
        alternatives = node.get("alternatives")
        if not isinstance(alternatives, list) or not alternatives:
            legacy = node.get("legacy_vector")
            self.fail(path, f"decompose has no constructive alternatives; legacy claim={legacy}")

        transition = node.get("transition")
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


def load_and_check(filename, *, allow_restarts=False):
    with open(filename, "r", encoding="utf-8") as stream:
        certificate = json.load(stream)
    if set(certificate) != {"format", "target", "proof"}:
        raise VerificationError("top-level fields are invalid")
    if certificate["format"] not in ("maxsat-local-proof-v1", "maxsat-local-proof-v2"):
        raise VerificationError("unknown certificate format")
    target = certificate["target"]
    if set(target) != {"numerator", "denominator"}:
        raise VerificationError("invalid target")
    legacy = certificate["format"] == "maxsat-local-proof-v1"
    checker = Checker(target["numerator"], target["denominator"], legacy=legacy, allow_restarts=allow_restarts)
    proof = certificate["proof"]
    # v1 encoded the initial family declaration as an exposure of []. It is
    # a declaration of the root family, never a coverage claim about [].
    if legacy and proof.get("rule") == "expose_variable":
        from .refine import declared_root
        proof = declared_root(proof, legacy=True)
    checker.check(proof)
    return checker
