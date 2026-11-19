from itertools import permutations

MAX_CLAUSES = 32767  # Semantic clause scores are stored as signed 16-bit integers.


def _literal(value):
    if type(value) is int:
        if abs(value) < 2:
            raise ValueError("ordinary variables must have IDs at least 2; use typed tails")
        return value

    if (isinstance(value, dict) and set(value) == {"tail", "kind"}
            and type(value["tail"]) is int
            and value["kind"] in ("any", "nonempty")):
        return ("tail", value["tail"], value["kind"])
    raise ValueError("literal must be an integer or a typed tail")


def _key(literal):
    return (0, literal) if type(literal) is int else (1, literal[1], literal[2])


def parse_formula(value):
    """Parse literals but preserve producer clause indices for refine rules."""
    if not isinstance(value, list):
        raise ValueError("formula must be a list of clauses")
    if len(value) > MAX_CLAUSES:
        raise ValueError(f"formula exceeds {MAX_CLAUSES} clauses")

    result = []
    for clause in value:
        if not isinstance(clause, list):
            raise ValueError("clause must be a list")
        parsed = [_literal(literal) for literal in clause]
        if len(set(parsed)) != len(parsed):
            raise ValueError("duplicate literal inside a clause")
        result.append(tuple(sorted(parsed, key=_key)))
    return tuple(result)


def sort_formula(formula):
    clauses = (tuple(sorted(clause, key=_key)) for clause in formula)
    return tuple(sorted(clauses, key=lambda clause: tuple(map(_key, clause))))


def is_tail(literal):
    # Parsed literals are either signed integers or tail tuples.
    return type(literal) is tuple


def tail_ids(formula):
    return sorted({literal[1] for clause in formula for literal in clause
                   if is_tail(literal)})


def variables(formula):
    return sorted({abs(literal) for clause in formula for literal in clause
                   if type(literal) is int})


def canonical_formula(formula):
    """Canonicalize ordinary variables and tail atoms independently."""
    formula = sort_formula(formula)
    ids = variables(formula)
    best = None

    for variable_targets in permutations(range(2, 2 + len(ids))):
        variable_map = dict(zip(ids, variable_targets))
        provisional = []
        for clause in formula:
            mapped_clause = []
            for literal in clause:
                if is_tail(literal):
                    mapped_clause.append(literal)
                else:
                    image = variable_map[abs(literal)]
                    mapped_clause.append(-image if literal < 0 else image)

            # Tail identities must not influence clause order.  The producer
            # currently has clause-local atoms; first-occurrence renaming then
            # preserves their equality pattern without a factorial search.
            signature = tuple(sorted(
                ((0, x) if type(x) is int else (1, x[2]))
                for x in mapped_clause))
            provisional.append((signature, mapped_clause))
        provisional.sort(key=lambda item: item[0])

        tail_map = {}
        mapped = []
        for _, clause in provisional:
            mapped_clause = []
            for literal in sorted(clause, key=_key):
                if is_tail(literal):
                    if literal[1] not in tail_map:
                        tail_map[literal[1]] = len(tail_map)
                    mapped_clause.append(("tail", tail_map[literal[1]], literal[2]))
                else:
                    mapped_clause.append(literal)
            mapped.append(mapped_clause)

        representation = sort_formula(mapped)
        if best is None or repr(representation) < repr(best):
            best = representation

    return best


def assignment_residual(formula, variable, value):
    result = []
    offset = decrease = 0

    for clause in formula:
        satisfied = False
        remaining = []
        for literal in clause:
            if is_tail(literal) or abs(literal) != variable:
                remaining.append(literal)
            elif value != (literal < 0):
                satisfied = True
                break

        if satisfied:
            offset += 1
            decrease += 1
        elif not remaining:
            decrease += 1
        elif all(is_tail(literal) for literal in remaining):
            # It leaves the bounded neighbourhood but remains in the global
            # recursive instance, hence does not contribute to decrease.
            pass
        else:
            result.append(remaining)

    return sort_formula(result), offset, decrease


def replace_tail(formula, clause_index, replacement):
    result = [list(clause) for clause in formula]
    if type(clause_index) is not int or not 0 <= clause_index < len(result):
        raise ValueError("tail split clause out of range")
    candidates = [literal for literal in result[clause_index]
                  if is_tail(literal) and literal[2] == "any"]
    if len(candidates) != 1:
        raise ValueError("tail split needs exactly one any-tail")

    old = candidates[0]
    result[clause_index].remove(old)
    if replacement is not None:
        result[clause_index].append(("tail", old[1], replacement))
    return sort_formula(result)
