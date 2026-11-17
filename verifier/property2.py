"""Local guards for the imported Property 2 in Xiao's reduced Step 6 context.

Global reducedness and the hidden-variable family remain explicit imported
premises; a partial formula cannot certify the absence of hidden reductions.
"""
from .formula import is_tail, normalize_formula, variables

STEP6_DEGREES = [[2, 2, False], [3, 1, True], [4, 1, True]]


def property2_sides(formula, variable):
    f = normalize_formula(formula)
    if type(variable) is not int or variable < 2:
        raise ValueError('Property 2 needs an ordinary pivot')
    stats = {}
    for v in variables(f):
        p = [c for c in f if v in c]
        n = [c for c in f if -v in c]
        if any(v in c and -v in c for c in f):
            raise ValueError('Property 2 needs a non-tautological Step 6 instance')
        ordinary = len(p) == len(n) == 2
        singleton = ((len(p) in (3, 4) and n == [(-v,)]) or
                     (len(n) in (3, 4) and p == [(v,)]))
        if not ordinary and not singleton:
            raise ValueError('known variable is outside the Step 6 family')
        if ordinary:
            for c in p + n:
                known = sum(type(lit) is int for lit in c)
                if known < 2 and not any(is_tail(lit) for lit in c):
                    raise ValueError('Step 4 must exclude unit (2,2) clauses first')
        stats[v] = ordinary
    if not stats.get(variable):
        raise ValueError('Property 2 needs a (2,2) pivot')
    return [any(literal in c and any(type(v) is int and abs(v) != variable and
                                    stats[abs(v)] for v in c) for c in f)
            for literal in (variable, -variable)]


def property1_sides(formula, variable, exclusions, scope):
    from .refine import checked_degree_scope, degree_is_covered
    scope = checked_degree_scope(scope)
    if any(not degree_is_covered(tuple(d), STEP6_DEGREES) for d in scope):
        raise ValueError('Property 1 degree scope is outside Step 6')
    property2_sides(formula, variable) # validate common reduced-Step-6 guards
    f = normalize_formula(formula)
    result = []
    for pivot_literal in (variable, -variable):
        valid = True
        for clause in f:
            if pivot_literal not in clause: continue
            for literal in clause:
                if type(literal) is int and abs(literal) != variable:
                    positive = sum(literal in c for c in f)
                    negative = [c for c in f if -literal in c]
                    valid &= positive == 3 and negative == [(-literal,)]
                elif is_tail(literal):
                    forbidden = exclusions.get(literal[1], ())
                    for p, n, singleton in scope:
                        if (p,n,singleton) == (3,1,True): continue
                        valid &= any(p == ep and n == en and (not es or singleton)
                                     for ep,en,es in forbidden)
        result.append(bool(valid))
    return result
