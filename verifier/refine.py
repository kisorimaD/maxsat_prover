from itertools import combinations

from .formula import (is_tail, normalize_formula, ordered_formula,
                      replace_tail, tail_ids, variables, canonical_formula)


POSSIBLE_DEGREES = (
    (3, 1, True), (2, 2, False), (3, 2, False), (2, 3, False), (4, 1, True),
)
LEGACY_DEGREES = ((1, 3, True), (1, 4, True)) + POSSIBLE_DEGREES


def validate_degree(positive, negative, singleton, legacy=False):
    if (type(positive) is not int or type(negative) is not int or
            positive < 1 or negative < 1 or positive + negative > 30 or
            type(singleton) is not bool):
        raise ValueError("invalid exposure degrees")
    if singleton and negative != 1 and not legacy:
        raise ValueError("singleton requires negative degree 1")


def degree_is_covered(degree, family):
    positive, negative, singleton = degree
    return any(positive == p and negative == n and (not s or singleton)
               for p, n, s in family)


def checked_degree_scope(scope):
    if not isinstance(scope, list) or not scope:
        raise ValueError("lemma degree scope must be a nonempty degree family")
    for degree in scope:
        if not isinstance(degree, list) or len(degree) != 3:
            raise ValueError("invalid lemma degree scope")
        validate_degree(*degree)
    return scope


def binding_degrees_covered(expression, parent, scope):
    for literal in expression:
        if type(literal) is not int:
            continue
        positive = sum(literal in clause for clause in parent)
        negative = sum(-literal in clause for clause in parent)
        singleton = negative == 1 and (-literal,) in parent
        if not degree_is_covered((positive, negative, singleton), scope):
            return False
    return True


def validate_exposure_formula(formula, variable):
    if type(variable) is not int or variable < 2 or variable in variables(formula):
        raise ValueError("exposure requires a fresh ordinary variable")
    seen = set()
    for clause in formula:
        tails = [lit for lit in clause if is_tail(lit)]
        if len(tails) > 1 or any(lit[1] in seen for lit in tails):
            raise ValueError("exposure requires clause-local single tails")
        seen.update(lit[1] for lit in tails)


def _build_formula(formula, roles, variable, positive, negative, singleton):
    result = []
    placed_positive = placed_negative = 0
    for clause, role in zip(formula, roles):
        new_clause = list(clause)
        if role in (1, -1):
            for index, literal in enumerate(new_clause):
                if is_tail(literal) and literal[2] == "nonempty":
                    new_clause[index] = ("tail", literal[1], "any")
            new_clause.append(variable if role == 1 else -variable)
            placed_positive += role == 1
            placed_negative += role == -1
        result.append(new_clause)
    next_tail = max(tail_ids(formula), default=-1) + 1
    for _ in range(positive - placed_positive):
        result.append([("tail", next_tail, "any"), variable])
        next_tail += 1
    for _ in range(negative - placed_negative):
        tail = [-variable]
        if not singleton:
            tail.append(("tail", next_tail, "any"))
            next_tail += 1
        result.append(tail)
    return normalize_formula([list(clause) for clause in result])


def generate_exposure(formula, variable, positive, negative, singleton,
                      required_clause=None, legacy=False, exclusions=None):
    validate_degree(positive, negative, singleton, legacy)
    validate_exposure_formula(formula, variable)
    wildcard_indices = [index for index, clause in enumerate(formula)
                        if any(is_tail(literal) for literal in clause)]
    generated = set()
    # Enumerate only placements within the declared degrees. Scanning all
    # 3^number_of_tails role vectors discarded almost everything at depth 5.
    required = () if required_clause is None else (required_clause,)
    if required_clause is not None and required_clause not in wildcard_indices:
        return generated
    available = [i for i in wildcard_indices if i not in required]
    for count_positive in range(min(positive - len(required), len(available)) + 1):
        for chosen_positive in combinations(available, count_positive):
            positives = set(required + chosen_positive)
            remaining = [i for i in available if i not in positives]
            max_negative = 0 if singleton else min(negative, len(remaining))
            for count_negative in range(max_negative + 1):
                for chosen_negative in combinations(remaining, count_negative):
                    roles = [0] * len(formula)
                    for i in positives: roles[i] = 1
                    for i in chosen_negative: roles[i] = -1
                    child = _build_formula(formula, roles, variable, positive, negative, singleton)
                    if exclusions:
                        from .typed_tails import restrict_exposure
                        child = restrict_exposure(child, variable, positive, negative, exclusions)
                    if child is not None: generated.add(child)
    return generated


def expected_children(node, legacy=False, exclusions=None):
    # Clause indices in refine records refer to the producer's original
    # sequence, so validate here but do not sort before applying the split.
    normalize_formula(node["formula"])
    formula = ordered_formula(node["formula"])
    rule = node["rule"]
    if rule == "expose_type_at_clause":
        from .typed_tails import expected_states, read_exclusions
        return {f for f, _ in expected_states(node, exclusions if exclusions is not None
                                             else read_exclusions(node), legacy=legacy)}
    if rule == "tail_empty_or_nonempty":
        clause = node["clause"]
        return {replace_tail(formula, clause, None),
                replace_tail(formula, clause, "nonempty")}
    if rule == "expose_variable":
        raise ValueError("unconditional exposure is only a root family declaration")
    if rule == "expose_at_clause":
        index = node["clause"]
        if type(index) is not int or not 0 <= index < len(formula):
            raise ValueError("exposure clause out of range")
        selected = formula[index]
        tails = [lit for lit in selected if is_tail(lit)]
        if len(tails) != 1 or not any(type(lit) is int for lit in selected):
            raise ValueError("exposure requires one tail and an active literal")
        result = ({replace_tail(formula, index, None)}
                  if tails[0][2] == "any" else set())
        degrees = node.get("degrees", LEGACY_DEGREES if legacy else POSSIBLE_DEGREES)
        if not isinstance(degrees, (list, tuple)) or not degrees:
            raise ValueError("exposure needs a nonempty degree specification")
        for positive, negative, singleton in degrees:
            result.update(generate_exposure(formula, node["variable"],
                                            positive, negative, singleton,
                                            index, legacy=legacy, exclusions=exclusions))
        return result
    raise ValueError(f"unknown refine rule {rule!r}")


def declared_root(node, legacy=False):
    """Decode the producer's initial family declaration, not a refinement."""
    fields = {"kind", "formula", "variable", "positive", "negative", "singleton", "children"}
    if legacy:
        fields.add("rule")
    if (set(node) != fields or node["kind"] != ("refine" if legacy else "root_family") or
            (legacy and node["rule"] != "expose_variable")):
        raise ValueError("invalid root family declaration")
    if node.get("formula") != [] or len(node.get("children", [])) != 1:
        raise ValueError("root declaration needs an empty seed and exactly one child")
    expected = generate_exposure((), node["variable"], node["positive"],
                                 node["negative"], node["singleton"], legacy=legacy)
    child = node["children"][0]
    if {canonical_formula(f) for f in expected} != {canonical_formula(child["formula"])}:
        raise ValueError("root family differs from its declared degrees")
    return child
