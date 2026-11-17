"""Structural knowledge about types of still-hidden literals in tail atoms.

These constraints are used only across structural refinements. Strategy
transitions may forget them: assignments/resolutions change hidden degrees.
"""
from itertools import permutations
from functools import lru_cache

from .formula import (is_tail, normalize_formula, ordered_formula, tail_ids,
                      variables)


def read_exclusions(node):
    from .refine import validate_degree
    records = node.get('tail_exclusions', [])
    if not isinstance(records, list):
        raise ValueError('tail_exclusions must be a list')
    tails = set(tail_ids(ordered_formula(node['formula'])))
    result = {}
    for record in records:
        if not isinstance(record, dict) or set(record) != {'tail', 'types'}:
            raise ValueError('invalid tail exclusion record')
        tail, types = record['tail'], record['types']
        if type(tail) is not int or tail not in tails or tail in result:
            raise ValueError('tail exclusions need distinct existing tail IDs')
        if not isinstance(types, list) or not types:
            raise ValueError('tail exclusion needs a nonempty type family')
        checked = set()
        for degree in types:
            if not isinstance(degree, list) or len(degree) != 3:
                raise ValueError('invalid excluded degree')
            validate_degree(*degree)
            if tuple(degree) in checked:
                raise ValueError('duplicate excluded degree')
            checked.add(tuple(degree))
        result[tail] = frozenset(checked)
    return result


def encode_exclusions(exclusions):
    return [{'tail': tail, 'types': [list(d) for d in sorted(types)]}
            for tail, types in sorted(exclusions.items()) if types]


def retained_exclusions(formula, exclusions):
    return {tail: types for tail, types in exclusions.items()
            if tail in tail_ids(formula)}


def canonical_state(formula, exclusions):
    """Canonicalize formula and tail colours together, including renamed atoms."""
    formula = normalize_formula(formula)
    colours = tuple((tail, tuple(sorted(types))) for tail, types in sorted(exclusions.items()))
    return _canonical_state_cached(formula, colours)


@lru_cache(maxsize=32768)
def _canonical_state_cached(formula, colours):
    # All keys and values are immutable. Rechecking a saved proof must not
    # repeat the factorial variable-renaming search for every attachment.
    exclusions = dict(colours)
    ids = variables(formula)
    best = None
    for targets in permutations(range(2, 2 + len(ids))):
        mapping = dict(zip(ids, targets))
        clauses = []
        for clause in formula:
            mapped = [(0, mapping[abs(v)] * (1 if v > 0 else -1)) if type(v) is int
                      else (1, v[1], v[2], tuple(sorted(exclusions.get(v[1], ()))))
                      for v in clause]
            signature = tuple(sorted((v if v[0] == 0 else (1, v[2], v[3])) for v in mapped))
            clauses.append((signature, mapped))
        clauses.sort(key=lambda c: c[0])
        names, result = {}, []
        for _, clause in clauses:
            row = []
            for v in sorted(clause):
                if v[0] == 0:
                    row.append(v)
                else:
                    if v[1] not in names: names[v[1]] = len(names)
                    row.append((1, names[v[1]], v[2], v[3]))
            result.append(tuple(sorted(row)))
        result = tuple(sorted(result))
        if best is None or result < best: best = result
    return best


def restrict_exposure(child, variable, positive, negative, exclusions):
    """Intersect a witness placement with all parent tail exclusions."""
    result = [list(c) for c in child]
    for clause in child:
        for literal in (variable, -variable):
            if literal not in clause: continue
            p, n = (positive, negative) if literal > 0 else (negative, positive)
            for tail in (v[1] for v in clause if is_tail(v)):
                for ep, en, singleton in exclusions.get(tail, ()):
                    if (ep, en) != (p, n): continue
                    if not singleton: return None
                    if n != 1: continue
                    for opposite in result:
                        if -literal not in opposite: continue
                        if sum(type(v) is int for v in opposite) > 1: continue
                        tails = [v for v in opposite if is_tail(v)]
                        if not tails: return None
                        if len(tails) != 1:
                            raise ValueError('singleton exclusion needs one opposite tail')
                        opposite[opposite.index(tails[0])] = ('tail', tails[0][1], 'nonempty')
    return normalize_formula(result)


def expected_states(node, exclusions, legacy=False):
    from .refine import (expected_children, generate_exposure, validate_degree,
                         validate_exposure_formula, checked_degree_scope)
    if node['rule'] != 'expose_type_at_clause':
        return [(f, retained_exclusions(f, exclusions))
                for f in expected_children(node, legacy=legacy, exclusions=exclusions)]
    formula = ordered_formula(node['formula'])
    variable, index = node['variable'], node['clause']
    validate_exposure_formula(formula, variable)
    if type(index) is not int or not 0 <= index < len(formula):
        raise ValueError('expose_type clause out of range')
    clause = formula[index]
    tails = [v for v in clause if is_tail(v)]
    if len(tails) != 1 or not any(type(v) is int for v in clause):
        raise ValueError('expose_type needs an active literal and one tail')
    degree = node['degree']
    if not isinstance(degree, list) or len(degree) != 3:
        raise ValueError('invalid expose_type degree')
    validate_degree(*degree)
    scope = checked_degree_scope(node['degrees'])
    if degree not in scope:
        raise ValueError('expose_type degree is outside the current degree family')
    children = [(f, retained_exclusions(f, exclusions)) for f in generate_exposure(
        formula, variable, *degree, required_clause=index, legacy=legacy,
        exclusions=exclusions)]
    absent = dict(exclusions)
    absent[tails[0][1]] = frozenset(set(absent.get(tails[0][1], ())) | {tuple(degree)})
    children.append((normalize_formula(node['formula']), absent))
    return children
