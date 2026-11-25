from itertools import product

from .formula import is_tail, replace_tail, sort_formula, tail_ids, variables


def validate_degree(positive, negative, singleton):
    if (type(positive) is not int or type(negative) is not int or
            positive < 1 or negative < 1 or positive + negative > 30 or
            type(singleton) is not bool):
        raise ValueError("invalid exposure degrees")
    if singleton and negative != 1:
        raise ValueError("singleton requires negative degree 1")


def parse_degrees(value):
    if not isinstance(value, list):
        raise ValueError("degree classes must be a list")
    degrees = set()
    for degree in value:
        if not isinstance(degree, list) or len(degree) != 3:
            raise ValueError("degree class must be a list of three values")
        validate_degree(*degree)
        degrees.add(tuple(degree))
    if len(degrees) != len(value):
        raise ValueError("duplicate degree class")
    return degrees


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

    return sort_formula(result)


def generate_exposure(formula, variable, positive, negative, singleton,
                      required_clause):
    wildcard_indices = [index for index, clause in enumerate(formula)
                        if any(is_tail(literal) for literal in clause)]
    generated = set()

    for choices in product((1, -1, 0), repeat=len(wildcard_indices)):
        roles = [0] * len(formula)
        for index, role in zip(wildcard_indices, choices):
            roles[index] = role
        if roles[required_clause] != 1:
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


def expected_children(node, formula, possible_degrees):
    rule = node["rule"]
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
        variable = node["variable"]
        validate_exposure_formula(formula, variable)

        degrees = parse_degrees(node["degrees"])
        if not degrees:
            raise ValueError("exposure needs a nonempty degree specification")
        if degrees != possible_degrees:
            raise ValueError("exposure degrees differ from possible_degrees")
        for positive, negative, singleton in degrees:
            result.update(generate_exposure(formula, variable,
                                            positive, negative, singleton,
                                            index))
        return result

    raise ValueError(f"unknown refine rule {rule!r}")
