from itertools import product

from .formula import (canonical_formula, check_variable_occurrences, is_tail,
                      normalize_formula, ordered_formula, replace_tail,
                      tail_ids, validate_maximum_clause_size,
                      validate_maximum_variable_occurrences, variables)


POSSIBLE_DEGREES = (
    (3, 1, True), (2, 2, False), (3, 2, False), (2, 3, False), (4, 1, True),
)
LEGACY_DEGREES = ((1, 3, True), (1, 4, True)) + POSSIBLE_DEGREES


def _limit_clause(clause, maximum_clause_size):
    if maximum_clause_size == -1:
        return tuple(clause)
    tails = [literal for literal in clause if is_tail(literal)]
    if len(tails) > 1:
        raise ValueError("a bounded structural clause must have at most one tail")
    known = {abs(literal) for literal in clause if type(literal) is int}
    if len(known) > maximum_clause_size:
        return None
    if tails and len(known) == maximum_clause_size:
        if tails[0][2] == "nonempty":
            return None
        return tuple(literal for literal in clause if not is_tail(literal))
    return tuple(clause)


def enforce_maximum_clause_size(formula, maximum_clause_size):
    """Return width-normalized formula, or None for an impossible case."""
    validate_maximum_clause_size(maximum_clause_size)
    formula = normalize_formula(formula) if isinstance(formula, list) else formula
    limited = []
    for clause in formula:
        child = _limit_clause(clause, maximum_clause_size)
        if child is None:
            return None
        limited.append(list(child))
    return normalize_formula(limited)


def validate_degree(positive, negative, singleton, legacy=False,
                    maximum_variable_occurrences=-1):
    validate_maximum_variable_occurrences(maximum_variable_occurrences)
    if (type(positive) is not int or type(negative) is not int or
            positive < 1 or negative < 1 or positive + negative > 30 or
            type(singleton) is not bool):
        raise ValueError("invalid exposure degrees")
    if singleton and negative != 1 and not legacy:
        raise ValueError("singleton requires negative degree 1")
    if (maximum_variable_occurrences != -1 and
            positive + negative > maximum_variable_occurrences):
        raise ValueError(
            "exposure degree exceeds maximum variable occurrences")


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
                      required_clause=None, legacy=False,
                      maximum_clause_size=-1,
                      maximum_variable_occurrences=-1):
    validate_maximum_clause_size(maximum_clause_size)
    validate_degree(positive, negative, singleton, legacy,
                    maximum_variable_occurrences)
    validate_exposure_formula(formula, variable)
    wildcard_indices = [index for index, clause in enumerate(formula)
                        if any(is_tail(literal) for literal in clause)]
    generated = set()
    for choices in product((1, -1, 0), repeat=len(wildcard_indices)):
        roles = [0] * len(formula)
        for index, role in zip(wildcard_indices, choices):
            roles[index] = role
        if required_clause is not None and roles[required_clause] != 1:
            continue
        placed_positive = roles.count(1)
        placed_negative = roles.count(-1)
        if placed_positive > positive or placed_negative > negative:
            continue
        if singleton and placed_negative:
            continue
        child = enforce_maximum_clause_size(
            _build_formula(formula, roles, variable,
                           positive, negative, singleton),
            maximum_clause_size)
        if child is not None:
            check_variable_occurrences(
                child, maximum_variable_occurrences)
            generated.add(child)
    return generated


def expected_children(node, legacy=False, maximum_clause_size=-1,
                      maximum_variable_occurrences=-1):
    validate_maximum_clause_size(maximum_clause_size)
    validate_maximum_variable_occurrences(maximum_variable_occurrences)
    # Clause indices in refine records refer to the producer's original
    # sequence, so validate here but do not sort before applying the split.
    normalize_formula(node["formula"])
    formula = ordered_formula(node["formula"])
    check_variable_occurrences(formula, maximum_variable_occurrences)
    if maximum_clause_size != -1:
        for parent_clause in formula:
            limited = _limit_clause(parent_clause, maximum_clause_size)
            if limited is None or limited != parent_clause:
                raise ValueError("parent formula is not width-normalized")
    rule = node["rule"]
    if rule == "tail_empty_or_nonempty":
        clause = node["clause"]
        result = set()
        for replacement in (None, "nonempty"):
            child = enforce_maximum_clause_size(
                replace_tail(formula, clause, replacement),
                maximum_clause_size)
            if child is not None:
                check_variable_occurrences(
                    child, maximum_variable_occurrences)
                result.add(child)
        return result
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
        result = set()
        if tails[0][2] == "any":
            empty_child = enforce_maximum_clause_size(
                replace_tail(formula, index, None), maximum_clause_size)
            if empty_child is not None:
                check_variable_occurrences(
                    empty_child, maximum_variable_occurrences)
                result.add(empty_child)
        degrees = node.get("degrees", LEGACY_DEGREES if legacy else POSSIBLE_DEGREES)
        if not isinstance(degrees, (list, tuple)) or not degrees:
            raise ValueError("exposure needs a nonempty degree specification")
        for positive, negative, singleton in degrees:
            result.update(generate_exposure(formula, node["variable"],
                                            positive, negative, singleton,
                                            index, legacy=legacy,
                                            maximum_clause_size=maximum_clause_size,
                                            maximum_variable_occurrences=
                                            maximum_variable_occurrences))
        return result
    raise ValueError(f"unknown refine rule {rule!r}")


def declared_root(node, legacy=False, maximum_clause_size=-1,
                  maximum_variable_occurrences=-1):
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
                                 node["negative"], node["singleton"], legacy=legacy,
                                 maximum_clause_size=maximum_clause_size,
                                 maximum_variable_occurrences=
                                 maximum_variable_occurrences)
    child = node["children"][0]
    if {canonical_formula(f) for f in expected} != {canonical_formula(child["formula"])}:
        raise ValueError("root family differs from its declared degrees")
    return child
