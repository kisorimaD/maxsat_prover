from itertools import permutations, product

MAX_CLAUSES = 32767


def check_formula_size(formula):
    if len(formula) > MAX_CLAUSES:
        raise ValueError(f"formula exceeds {MAX_CLAUSES} clauses")


def _literal(value):
    if (isinstance(value, tuple) and len(value) == 3 and value[0] == "tail"
            and type(value[1]) is int and value[2] in ("any", "nonempty")):
        return value
    if type(value) is int:
        if value in (0, 1):
            # Kept only for small legacy unit tests.  Real certificates use
            # stable tail objects.
            return ("tail", value, "nonempty" if value == 1 else "any")
        return value
    if (isinstance(value, dict) and set(value) == {"tail", "kind"}
            and type(value["tail"]) is int
            and value["kind"] in ("any", "nonempty")):
        return ("tail", value["tail"], value["kind"])
    raise ValueError("literal must be an integer or a typed tail")


def _key(literal):
    return (0, literal) if type(literal) is int else (1, literal[1], literal[2])


def normalize_formula(value):
    if isinstance(value, (list, tuple)):
        check_formula_size(value)
    if not isinstance(value, list):
        # Internal normalized formulas can safely be passed through.
        if isinstance(value, tuple):
            return value
        raise ValueError("formula must be a list of clauses")
    clauses = []
    for clause in value:
        if not isinstance(clause, list):
            raise ValueError("clause must be a list")
        parsed = [_literal(literal) for literal in clause]
        if len(set(parsed)) != len(parsed):
            raise ValueError("duplicate literal inside a clause")
        clauses.append(tuple(sorted(parsed, key=_key)))
    return tuple(sorted(clauses, key=lambda clause: tuple(_key(x) for x in clause)))


def ordered_formula(value):
    """Parse literals but preserve producer clause indices for refine rules."""
    if not isinstance(value, list):
        raise ValueError("formula must be a list of clauses")
    check_formula_size(value)
    result = []
    for clause in value:
        if not isinstance(clause, list):
            raise ValueError("clause must be a list")
        parsed = [_literal(literal) for literal in clause]
        if len(set(parsed)) != len(parsed):
            raise ValueError("duplicate literal inside a clause")
        result.append(tuple(sorted(parsed, key=_key)))
    return tuple(result)


def is_tail(literal):
    return type(literal) is tuple and len(literal) == 3 and literal[0] == "tail"


def contains_tail(formula):
    return any(is_tail(literal) for clause in formula for literal in clause)


def tail_ids(formula):
    return sorted({literal[1] for clause in formula for literal in clause
                   if is_tail(literal)})


def variables(formula):
    return sorted({abs(literal) for clause in formula for literal in clause
                   if type(literal) is int})


def canonical_formula(formula):
    """Canonicalize ordinary variables and tail atoms independently."""
    if not isinstance(formula, tuple):
        formula = normalize_formula(formula)
    ids = variables(formula)
    variable_permutations = permutations(range(2, 2 + len(ids))) if ids else [()]
    best = None
    for variable_targets in variable_permutations:
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
            mapped.append(tuple(sorted(mapped_clause, key=_key)))
        representation = tuple(sorted(mapped,
                                      key=lambda c: tuple(_key(x) for x in c)))
        if best is None or repr(representation) < repr(best):
            best = representation
    return best if best is not None else formula


def satisfied_clauses(formula, assignment, boundary):
    total = 0
    for clause in formula:
        clause_true = False
        for literal in clause:
            if is_tail(literal):
                clause_true |= boundary[literal[1]]
            else:
                value = assignment[abs(literal)]
                clause_true |= value != (literal < 0)
            if clause_true:
                break
        total += clause_true
    return total


def optimum(formula, boundary=None):
    formula = normalize_formula(formula) if isinstance(formula, list) else formula
    boundary = {} if boundary is None else boundary
    missing = set(tail_ids(formula)) - set(boundary)
    if missing:
        raise ValueError(f"missing boundary values for tails {sorted(missing)}")
    ids = variables(formula)
    best = 0
    for values in product((False, True), repeat=len(ids)):
        assignment = dict(zip(ids, values))
        best = max(best, satisfied_clauses(formula, assignment, boundary))
    return best


def assignment_residual(formula, variable, value, keep_tail_only=False):
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
        elif all(is_tail(literal) for literal in remaining) and not keep_tail_only:
            # It leaves the bounded neighbourhood but remains in the global
            # recursive instance, hence does not contribute to decrease.
            pass
        else:
            result.append(remaining)
    return tuple(sorted((tuple(sorted(c, key=_key)) for c in result),
                        key=lambda c: tuple(_key(x) for x in c))), offset, decrease


def all_boundary_assignments(*formulas):
    ids = sorted(set().union(*(set(tail_ids(formula)) for formula in formulas)))
    for values in product((False, True), repeat=len(ids)):
        yield dict(zip(ids, values))


def replace_tail(formula, clause_index, replacement):
    result = [list(clause) for clause in formula]
    if not 0 <= clause_index < len(result):
        raise ValueError("tail split clause out of range")
    candidates = [literal for literal in result[clause_index]
                  if is_tail(literal) and literal[2] == "any"]
    if len(candidates) != 1:
        raise ValueError("tail split needs exactly one any-tail")
    old = candidates[0]
    result[clause_index].remove(old)
    if replacement is not None:
        result[clause_index].append(("tail", old[1], replacement))
    return tuple(sorted((tuple(sorted(c, key=_key)) for c in result),
                        key=lambda c: tuple(_key(x) for x in c)))
