from itertools import product

from .formula import (is_tail, normalize_formula, ordered_formula,
                      replace_tail, tail_ids)


POSSIBLE_DEGREES = (
    (1, 3, True), (3, 1, True), (2, 2, False),
    (3, 2, False), (2, 3, False), (1, 4, True), (4, 1, True),
)


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
                      required_clause=None):
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
        generated.add(_build_formula(formula, roles, variable,
                                     positive, negative, singleton))
    return generated


def expected_children(node):
    # Clause indices in refine records refer to the producer's original
    # sequence, so validate here but do not sort before applying the split.
    normalize_formula(node["formula"])
    formula = ordered_formula(node["formula"])
    rule = node["rule"]
    if rule == "tail_empty_or_nonempty":
        clause = node["clause"]
        return {replace_tail(formula, clause, None),
                replace_tail(formula, clause, "nonempty")}
    if rule == "expose_variable":
        return generate_exposure(formula, node["variable"],
                                 node["positive"], node["negative"],
                                 node["singleton"])
    if rule == "expose_at_clause":
        result = {replace_tail(formula, node["clause"], None)}
        for positive, negative, singleton in POSSIBLE_DEGREES:
            result.update(generate_exposure(formula, node["variable"],
                                            positive, negative, singleton,
                                            node["clause"]))
        return result
    raise ValueError(f"unknown refine rule {rule!r}")
