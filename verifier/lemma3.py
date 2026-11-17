"""The explicit short alternative of Xiao Lemma 3 (still an import)."""
from .formula import is_tail, normalize_formula


def resolution_alternative(formula, variable):
    formula = normalize_formula(formula)
    if type(variable) is not int or variable < 2:
        raise ValueError('lemma3 needs an ordinary variable')
    positive = [i for i, c in enumerate(formula) if variable in c]
    negative = [i for i, c in enumerate(formula) if -variable in c]
    if (len(positive), len(negative)) not in ((2, 1), (1, 2)):
        raise ValueError('lemma3 needs exactly a (2,1) variable')
    twice, once = (positive, negative) if len(positive) == 2 else (negative, positive)
    incident = set(twice + once)
    if len(incident) != 3:
        raise ValueError('lemma3 occurrences must be in three distinct clauses')
    D = [v for v in formula[once[0]] if is_tail(v) or abs(v) != variable]
    minimum_D = len({abs(v) for v in D if type(v) is int}) + int(
        any(is_tail(v) and v[2] == 'nonempty' for v in D))
    result = [list(c) for i, c in enumerate(formula) if i not in incident]
    for i in twice:
        C = [v for v in formula[i] if is_tail(v) or abs(v) != variable]
        ordinary = {v for v in C + D if type(v) is int}
        tails = {}
        for v in C + D:
            if is_tail(v):
                tails[v[1]] = tails.get(v[1], False) or v[2] == 'nonempty'
        result.append(list(ordinary) + [('tail', t, 'nonempty' if nonempty else 'any')
                                       for t, nonempty in tails.items()])
    return normalize_formula(result), max(8, 7 + 2 * minimum_D)
