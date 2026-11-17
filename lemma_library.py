"""Resolve proof-backed lemma leaves during certificate assembly.

The checker does not trust this module: it independently checks the context
embedding and every node of the attached proof. No standalone q test is made.
"""

import json
import hashlib
from pathlib import Path

from verifier.formula import is_tail, ordered_formula, tail_ids, variables
from verifier.arithmetic import target_fraction, vector_weight
from verifier.refine import checked_degree_scope, degree_is_covered, binding_degrees_covered


PROOF_FILES = {"step5.1": Path(__file__).resolve().parent / "lemmas" / "step5.1.json"}


def step6_context_mask(definition):
    """Global Properties may be reused only before any semantic transition.

    Structural refinement and local_context preserve the complete instance.
    Assignments, RR and resolution do not preserve its reduced Step 6 class.
    """
    names = {a.get('name') for a in definition.get('premises', {}).get('imports', [])}
    mask = int('xiao_property1' in names) | (2 * int('xiao_property2' in names))
    if not mask:
        return 0
    def visit(node, allowed=True):
        kind = node.get('kind')
        if kind in ('xiao_property1_branch', 'xiao_property2_branch') and not allowed:
            raise ValueError('Xiao Properties 1/2 need a global Xiao-reduced context; semantic transitions cannot retain it')
        retained = allowed and kind in ('strategy', 'refine', 'local_context')
        if 'proof' in node: visit(node['proof'], retained)
        for child in node.get('children', []): visit(child, retained)
        for alternative in node.get('alternatives', []): visit(alternative['proof'], False)
    visit(definition['proof'])
    return mask


def validate_step6_application(application):
    from verifier.formula import normalize_formula
    from verifier.property2 import property2_sides, STEP6_DEGREES
    parent = normalize_formula(application['formula'])
    pivot = next((v for v in variables(parent)
                  if sum(v in c for c in parent) == sum(-v in c for c in parent) == 2), None)
    if pivot is None:
        raise ValueError('global Xiao-reduced context needs a known (2,2) pivot')
    property2_sides(parent, pivot)  # Independently checks every known variable and unit22.
    scope = checked_degree_scope(application.get('degree_scope'))
    if any(not degree_is_covered(d, STEP6_DEGREES) for d in scope):
        raise ValueError('saved Xiao property lemma needs the Step 6 degree scope')


def definition_digest(definition):
    return hashlib.sha256(json.dumps(definition, sort_keys=True, separators=(",", ":"),
                                    ensure_ascii=False, allow_nan=False).encode()).hexdigest()


def _legacy_step51_roles(formula):
    for variable in variables(formula):
        positive = [c for c in formula if variable in c]
        negative = [c for c in formula if -variable in c]
        if len(positive) == 3 and len(negative) == 2 and (-variable,) in negative:
            return [variable]
        if len(negative) == 3 and len(positive) == 2 and (variable,) in positive:
            return [-variable]
    raise ValueError("legacy step5.1 application has no matching configuration")


def _proof_variables(proof):
    result = set(variables(ordered_formula(proof["formula"])))
    if "variable" in proof:
        result.add(proof["variable"])
    if "proof" in proof:
        result.update(_proof_variables(proof["proof"]))
    for child in proof.get("children", []):
        result.update(_proof_variables(child))
    for alternative in proof.get("alternatives", []):
        result.update(_proof_variables(alternative["proof"]))
    return result


def _has_structural_refinement(proof):
    if proof.get('kind') == 'refine':
        return True
    nested = ([proof['proof']] if 'proof' in proof else []) + proof.get('children', [])
    nested += [a['proof'] for a in proof.get('alternatives', [])]
    return any(_has_structural_refinement(child) for child in nested)


def _rename_proof(proof, variable_map, tail_shift):
    node = dict(proof)
    def rename_formula(formula):
        result = []
        for clause in ordered_formula(formula):
            mapped = []
            for lit in clause:
                if is_tail(lit):
                    mapped.append({"tail": lit[1] + tail_shift, "kind": lit[2]})
                else:
                    mapped.append(variable_map[abs(lit)] * (1 if lit > 0 else -1))
            result.append(mapped)
        return result
    node["formula"] = rename_formula(node["formula"])
    if "tail_exclusions" in node:
        node["tail_exclusions"] = [dict(record, tail=record["tail"] + tail_shift)
                                   for record in node["tail_exclusions"]]
    if "proof" in node:
        node["proof"] = _rename_proof(node["proof"], variable_map, tail_shift)
    if "children" in node:
        node["children"] = [_rename_proof(child, variable_map, tail_shift)
                            for child in node["children"]]
    if "alternatives" in node:
        node["alternatives"] = [dict(alternative) for alternative in node["alternatives"]]
        for alternative in node["alternatives"]:
            alternative["formula"] = rename_formula(alternative["formula"])
            alternative["proof"] = _rename_proof(alternative["proof"], variable_map, tail_shift)
    if "variable" in node:
        source_variable = node["variable"]
        node["variable"] = abs(variable_map[source_variable])
        if node.get("transition") == "assign" and variable_map[source_variable] < 0:
            node["alternatives"].reverse()
        if node.get("kind") == "xiao_property2_branch" and variable_map[source_variable] < 0:
            node["children"].reverse()
            node["imported_sides"] = list(reversed(node["imported_sides"]))
        if node.get("kind") == "xiao_property1_branch" and variable_map[source_variable] < 0:
            node["children"].reverse()
            node["properties"] = list(reversed(node["properties"]))
    if node.get("kind") == "lemma":
        node["roles"] = [variable_map[abs(lit)] * (1 if lit > 0 else -1)
                         for lit in node["roles"]]
    if node.get("kind") == "local_context":
        node["kept_variables"] = [abs(variable_map[var]) for var in node["kept_variables"]]
        if 'role_bindings' in node:
            node['role_bindings'] = [
                {'variable': abs(variable_map[b['variable']]),
                 'literal': (1 if variable_map[b['variable']] > 0 else -1) *
                            variable_map[abs(b['literal'])] * (1 if b['literal'] > 0 else -1)}
                for b in node['role_bindings']]
        node["clause_map"] = list(node["clause_map"])
        node["tail_bindings"] = [
            {"tail": binding["tail"] + tail_shift,
             "literals": rename_formula([binding["literals"]])[0]}
            for binding in node["tail_bindings"]]
    return node


def _attach_definition(application, definition):
    parent = ordered_formula(application["formula"])
    roles = application["roles"]
    source_roles = definition["roles"]
    if (not isinstance(roles, list) or len(roles) != len(source_roles) or
            any(type(lit) is not int or abs(lit) < 2 for lit in roles) or
            len({abs(lit) for lit in roles}) != len(roles) or
            not {abs(lit) for lit in roles}.issubset(variables(parent))):
        raise ValueError("invalid lemma role mapping")
    if application["vector"] != definition["vector"]:
        raise ValueError("lemma application vector differs from its definition")
    next_variable = max(variables(parent), default=1) + 1
    role_bindings = None
    if any(lit < 0 for lit in roles) and _has_structural_refinement(definition['proof']):
        # A polarity change need not preserve a quotient of structural cases
        # made modulo unsigned isomorphism. Keep the proved case tree in its
        # original orientation and bind fresh formal parameters instead.
        variable_map = {source: next_variable + index for index, source in
                        enumerate(sorted(_proof_variables(definition['proof'])))}
        role_bindings = {variable_map[source]: literal for source, literal in zip(source_roles, roles)}
    else:
        variable_map = dict(zip(source_roles, roles))
        for source in sorted(_proof_variables(definition["proof"]) - set(source_roles)):
            variable_map[source] = next_variable
            next_variable += 1
    tail_shift = max(tail_ids(parent), default=-1) + 1
    proof = _rename_proof(definition["proof"], variable_map, tail_shift)
    pattern = ordered_formula(proof["formula"])
    kept = {abs(lit) for lit in roles}
    if set(variables(pattern)) != (set(role_bindings) if role_bindings is not None else kept):
        raise ValueError("lemma root roles differ from its variables")
    available = {idx for idx, clause in enumerate(parent)
                 if any(type(lit) is int and abs(lit) in kept for lit in clause)}
    clause_map = [-1] * len(pattern)
    bindings = {}
    # Match exact clauses, then nonempty tails, then arbitrary tails. A loose
    # match must not consume the only witness for a more constrained clause.
    def constraint_rank(idx):
        tails = [lit for lit in pattern[idx] if is_tail(lit)]
        return 0 if not tails else (1 if tails[0][2] == "nonempty" else 2)
    order = sorted(range(len(pattern)), key=constraint_rank)
    for pattern_idx in order:
        clause = pattern[pattern_idx]
        explicit = {((role_bindings[abs(lit)] * (1 if lit > 0 else -1))
                     if role_bindings is not None else lit)
                    for lit in clause if type(lit) is int}
        tails = [lit for lit in clause if is_tail(lit)]
        if len(tails) > 1:
            raise ValueError("lemma root matching currently needs clause-local single tails")
        for original_idx in sorted(available):
            original = parent[original_idx]
            displayed = {lit for lit in original if type(lit) is int and abs(lit) in kept}
            if displayed != explicit:
                continue
            remainder = [lit for lit in original if lit not in displayed]
            if not tails and remainder:
                continue
            if "degree_scope" in application and not binding_degrees_covered(
                    remainder, parent, application["degree_scope"]):
                continue
            if tails and tails[0][2] == "nonempty" and not any(
                    type(lit) is int or lit[2] == "nonempty" for lit in remainder):
                continue
            if tails:
                tail = tails[0][1]
                if tail in bindings:
                    raise ValueError("lemma root matcher needs distinct clause-local tails")
                bindings[tail] = remainder
            clause_map[pattern_idx] = original_idx
            available.remove(original_idx)
            break
        if clause_map[pattern_idx] == -1:
            raise ValueError("lemma template does not match its local configuration")
    if available:
        raise ValueError("lemma template omits occurrences of a kept variable")
    witnesses = application.get("witness_clauses", [])
    exact_matches = {clause_map[idx] for idx, clause in enumerate(pattern)
                     if not any(is_tail(lit) for lit in clause)}
    if (not isinstance(witnesses, list) or
            any(type(idx) is not int or idx not in exact_matches for idx in witnesses)):
        raise ValueError("lemma witness is not an exact matched clause")
    def json_literals(expression):
        return [{"tail": lit[1], "kind": lit[2]} if is_tail(lit) else lit
                for lit in expression]
    attached = {"kind": "local_context", "lemma": definition["id"],
            "formula": application["formula"], "kept_variables": sorted(kept),
            "clause_map": clause_map,
            "tail_bindings": [{"tail": tail, "literals": json_literals(expression)}
                              for tail, expression in sorted(bindings.items())],
            "proof": proof}
    if role_bindings is not None:
        attached['role_bindings'] = [{'variable': var, 'literal': literal}
                                     for var, literal in sorted(role_bindings.items())]
    if "target" in definition:
        attached["target"] = dict(definition["target"])
    if "degree_scope" in application:
        attached["degree_scope"] = application["degree_scope"]
    return attached


def expand_lemma_applications(proof, definitions=None, target=None):
    definitions = (definitions if definitions is not None else
                   {name: json.loads(path.read_text()) for name, path in PROOF_FILES.items()})
    validated = set()
    def expand(node, stack=(), step6_allowed=True):
        if not isinstance(node, dict):
            raise ValueError("invalid proof node during lemma expansion")
        node = dict(node)
        if node.get("kind") == "assumption" and node.get("name") == "step5.1":
            # Previously emitted logs omitted roles. Recover this one precise
            # configuration so existing certificates can also shed the import.
            node["roles"] = _legacy_step51_roles(ordered_formula(node["formula"]))
            node["witness_clauses"] = []
            node["kind"] = "lemma"
        if node.get("kind") == "lemma":
            required = {"kind", "formula", "name", "roles", "witness_clauses", "vector"}
            if not required.issubset(node) or set(node) - required - {"definition_digest", "degree_scope"}:
                raise ValueError("invalid lemma application fields")
            name = node["name"]
            if name not in definitions:
                raise ValueError(f"missing proof definition for lemma {name!r}")
            if name in stack:
                raise ValueError(f"cyclic lemma proof dependency: {stack + (name,)}")
            definition = definitions[name]
            if step6_context_mask(definition):
                if not step6_allowed:
                    raise ValueError('Xiao Properties 1/2 need a global Xiao-reduced context; cannot apply a saved property lemma after a semantic transition')
                validate_step6_application(node)
            required_definition = {"id", "roles", "vector", "proof"}
            if (not required_definition.issubset(definition) or
                    set(definition) - required_definition - {"target", "premises"} or
                    definition["id"] != name):
                raise ValueError("invalid lemma proof definition")
            if "target" in definition:
                if name not in validated:
                    validate_saved_lemma(definition)
                    validated.add(name)
                bound_target = definition["target"]
                if (target is None or target_fraction(**bound_target) !=
                        target_fraction(**target)):
                    raise ValueError("saved lemma is only available at its fixed target q")
                if "definition_digest" in node and node["definition_digest"] != definition_digest(definition):
                    raise ValueError("saved lemma definition changed since generation")
                if "degree_scope" in node:
                    scope = checked_degree_scope(node["degree_scope"])
                    for premise in definition["premises"]["degrees"]:
                        if any(not degree_is_covered(degree, premise["degrees"]) for degree in scope):
                            raise ValueError("saved lemma does not cover the application degree scope")
            node = _attach_definition(node, definition)
            node["proof"] = expand(node["proof"], stack + (name,), step6_allowed)
            return node
        retained = step6_allowed and node.get('kind') in ('strategy', 'refine', 'local_context')
        if "proof" in node:
            node["proof"] = expand(node["proof"], stack, retained)
        if "alternatives" in node:
            node["alternatives"] = [dict(alternative, proof=expand(alternative["proof"], stack, False))
                                    for alternative in node["alternatives"]]
        if "children" in node:
            node["children"] = [expand(child, stack, retained) for child in node["children"]]
        return node
    return expand(proof)


def validate_saved_lemma(definition):
    """Check a fixed-q artifact without requiring its weight to be <= 1."""
    from verifier.check import Checker
    fields = {"id", "roles", "vector", "target", "premises", "proof"}
    if not isinstance(definition, dict) or set(definition) != fields:
        raise ValueError("invalid saved lemma definition fields")
    if not isinstance(definition["id"], str) or not definition["id"] or definition["id"] in PROOF_FILES:
        raise ValueError("invalid or reserved saved lemma identifier")
    target = definition["target"]
    if not isinstance(target, dict) or set(target) != {"numerator", "denominator"}:
        raise ValueError("invalid saved lemma target")
    roles = definition["roles"]
    if (not isinstance(roles, list) or roles != variables(ordered_formula(
            definition["proof"]["formula"]))):
        raise ValueError("saved lemma roles differ from its root variables")
    checker = Checker(**target)
    vector = checker._strategy(definition["proof"], "lemma.proof", 1)
    if vector_weight(vector, **target) != vector_weight(definition["vector"], **target):
        raise ValueError("saved lemma vector differs from its checked worst vector")
    premises = {"degrees": checker.degree_premises, "imports": checker.assumptions}
    # Normalize tuples in default degree families to their JSON representation.
    if definition.get("premises") != json.loads(json.dumps(premises)):
        raise ValueError("saved lemma premises differ from its proof")
    return checker


def save_session_lemma(proof, output_file, target):
    """Persist the complete case tree and its worst vector at one fixed q."""
    from verifier.check import Checker
    import os
    import tempfile
    checker = Checker(**target)
    vector = checker._strategy(proof, "lemma.proof", 1)
    definition = {
        "id": "session:" + Path(output_file).stem,
        "roles": variables(ordered_formula(proof["formula"])),
        "vector": vector,
        "target": dict(target),
        "premises": {"degrees": checker.degree_premises, "imports": checker.assumptions},
        "proof": proof,
    }
    # Write only after all coverage and semantic checks have succeeded.
    destination = Path(output_file)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                                         dir=destination.parent, delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(definition, stream, separators=(",", ":"), allow_nan=False)
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return definition
