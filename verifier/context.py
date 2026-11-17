"""Check a zero-cost change of local variables and boundary expressions.

Clauses outside the new neighbourhood stay in the complete recursive instance.
The child proof is universal over its tails; each tail is instantiated by the
recorded disjunction on forgotten variables and the parent's boundary atoms.
"""

from .formula import is_tail, ordered_formula, tail_ids, variables


def validate_property_contexts(proof, allowed=True, inside_context=False):
    """Check global-property reuse independently of the lemma assembler.

    Local abstraction retains the complete instance, while every semantic
    transition invalidates the original reduced Step 6 premise.
    """
    if not isinstance(proof, dict):
        raise ValueError('invalid proof in property-context validation')
    kind = proof.get('kind')
    direct = kind in ('xiao_property1_branch', 'xiao_property2_branch')
    if direct and inside_context and not allowed:
        raise ValueError('saved Xiao property needs a global Xiao-reduced context before semantic transitions')
    retained = allowed and kind in ('strategy', 'refine', 'local_context')
    nested = inside_context or kind == 'local_context'
    contains = direct
    if 'proof' in proof:
        contains |= validate_property_contexts(proof['proof'], retained, nested)
    for child in proof.get('children', []):
        contains |= validate_property_contexts(child, retained, nested)
    for alternative in proof.get('alternatives', []):
        contains |= validate_property_contexts(alternative['proof'], False, nested)
    if kind == 'local_context' and contains:
        if not allowed:
            raise ValueError('saved Xiao property cannot retain a global Xiao-reduced context after a semantic transition')
        from .property2 import property2_sides, STEP6_DEGREES
        from .refine import checked_degree_scope, degree_is_covered
        parent = ordered_formula(proof['formula'])
        pivot = next((v for v in variables(parent)
                      if sum(v in c for c in parent) == sum(-v in c for c in parent) == 2), None)
        if pivot is None:
            raise ValueError('saved Xiao property needs a known (2,2) pivot')
        property2_sides(parent,pivot)
        if any(not degree_is_covered(d,STEP6_DEGREES) for d in checked_degree_scope(proof.get('degree_scope'))):
            raise ValueError('saved Xiao property needs the Step 6 degree scope')
    return bool(contains)


def validate_local_context(node):
    required = {"kind", "formula", "kept_variables", "clause_map",
                "tail_bindings", "proof"}
    if not required.issubset(node) or set(node) - required - {"lemma", "target", "degree_scope", "role_bindings"}:
        raise ValueError("invalid local-context fields")
    if "lemma" in node and not isinstance(node["lemma"], str):
        raise ValueError("invalid local-context annotation")
    parent = ordered_formula(node["formula"])
    if not isinstance(node["proof"], dict):
        raise ValueError("local context needs a child proof")
    child = ordered_formula(node["proof"].get("formula"))
    kept = node["kept_variables"]
    if (not isinstance(kept, list) or not kept or
            any(type(var) is not int or var < 2 for var in kept) or
            len(set(kept)) != len(kept)):
        raise ValueError("invalid kept variables")
    kept = set(kept)
    if not kept.issubset(variables(parent)):
        raise ValueError("local-context variables do not match")
    role_map = {v: v for v in kept}
    if 'role_bindings' in node:
        records = node['role_bindings']
        if not isinstance(records, list) or len(records) != len(kept):
            raise ValueError('invalid local-context role bindings')
        role_map = {}
        for record in records:
            if not isinstance(record, dict) or set(record) != {'variable', 'literal'}:
                raise ValueError('invalid local-context role binding')
            formal, literal = record['variable'], record['literal']
            if (type(formal) is not int or formal < 2 or formal in role_map or
                    formal in variables(parent) or type(literal) is not int or abs(literal) not in kept):
                raise ValueError('role bindings need fresh distinct formal variables and kept literals')
            role_map[formal] = literal
        if {abs(v) for v in role_map.values()} != kept:
            raise ValueError('role bindings must bijectively cover the kept variables')
    if set(variables(child)) != set(role_map):
        raise ValueError('local-context formal variables do not match')

    clause_map = node["clause_map"]
    if (not isinstance(clause_map, list) or len(clause_map) != len(child) or
            any(type(idx) is not int or not 0 <= idx < len(parent)
                for idx in clause_map) or len(set(clause_map)) != len(clause_map)):
        raise ValueError("invalid local-context clause map")
    incident = {idx for idx, clause in enumerate(parent)
                if any(type(lit) is int and abs(lit) in kept for lit in clause)}
    if set(clause_map) != incident:
        raise ValueError("local context must retain every incident clause")

    bindings = {}
    records = node["tail_bindings"]
    if not isinstance(records, list):
        raise ValueError("invalid tail bindings")
    parent_tails = set(tail_ids(parent))
    for record in records:
        if not isinstance(record, dict) or set(record) != {"tail", "literals"}:
            raise ValueError("invalid tail binding")
        tail = record["tail"]
        if (type(tail) is not int or tail < 0 or tail in bindings or
                tail in parent_tails):
            raise ValueError("context tails must be distinct and fresh")
        expression = ordered_formula([record["literals"]])[0]
        if any(type(lit) is int and abs(lit) in kept for lit in expression):
            raise ValueError("tail binding contains a kept variable")
        bindings[tail] = expression
    if set(bindings) != set(tail_ids(child)):
        raise ValueError("tail bindings differ from the child boundary")

    if "degree_scope" in node:
        from .refine import checked_degree_scope, binding_degrees_covered
        scope = checked_degree_scope(node["degree_scope"])
        for expression in bindings.values():
            if not binding_degrees_covered(expression, parent, scope):
                raise ValueError("forgotten literal lies outside the lemma degree scope")

    forgotten = set(variables(parent)) if 'role_bindings' in node else set(variables(parent)) - kept
    def check_freshness(proof):
        if not isinstance(proof, dict):
            raise ValueError("invalid proof inside local context")
        if forgotten.intersection(variables(ordered_formula(proof.get("formula")))):
            raise ValueError("lemma proof captures a forgotten variable")
        if proof.get("variable") in forgotten:
            raise ValueError("lemma proof assigns a forgotten variable")
        if "proof" in proof:
            check_freshness(proof["proof"])
        for alternative in proof.get("alternatives", []):
            check_freshness(alternative["proof"])
        for nested in proof.get("children", []):
            check_freshness(nested)
    check_freshness(node["proof"])

    for child_clause, parent_idx in zip(child, clause_map):
        original = parent[parent_idx]
        expected_kept = {lit for lit in original
                         if type(lit) is int and abs(lit) in kept}
        actual_kept = {role_map[abs(lit)] * (1 if lit > 0 else -1)
                       for lit in child_clause if type(lit) is int}
        if actual_kept != expected_kept:
            raise ValueError("local context changes a kept literal")
        expected_tail = set(original) - expected_kept
        actual_tail = set()
        for literal in child_clause:
            if not is_tail(literal):
                continue
            expression = bindings[literal[1]]
            if literal[2] == "nonempty" and not any(
                    type(lit) is int or lit[2] == "nonempty" for lit in expression):
                raise ValueError("nonempty tail binding has no nonempty witness")
            actual_tail.update(expression)
        if actual_tail != expected_tail:
            raise ValueError("tail binding does not reconstruct the original clause")

    # No clauses have been removed from the complete formula. The wrapper
    # contributes zero offset/decrease, irrespective of the local size change.
