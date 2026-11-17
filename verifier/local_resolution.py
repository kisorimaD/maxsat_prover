"""Independently checked sufficient conditions for Chen/Xu resolutions."""
from .formula import normalize_formula, is_tail


def resolution_result(formula, variable, rule):
    f = normalize_formula(formula)
    if type(variable) is not int or variable < 2:
        raise ValueError('resolution requires an ordinary pivot')
    p = [i for i,c in enumerate(f) if variable in c]
    n = [i for i,c in enumerate(f) if -variable in c]
    block = set(p+n)
    if len(block) != len(p)+len(n):
        raise ValueError('pivot occurs with both signs in a clause')
    if rule == 'RR9':
        if (len(p),len(n)) != (2,2):
            raise ValueError('RR9 needs a (2,2) pivot')
        valid=False
        for side in (p,n):
            for v in f[side[0]]:
                if type(v) is not int or abs(v)==variable or v not in f[side[1]]:continue
                opposite=[c for c in f if -v in c]
                if len(opposite)==1 and opposite[0]==(-v,):valid=True
        if not valid:raise ValueError('RR9 needs a shared singleton with a unit complement')
        decrease=0
    elif rule == 'RR10':
        if (len(p),len(n)) != (2,2):
            raise ValueError('RR10 needs a (2,2) pivot')
        for i in block:
            witnesses = [v for v in f[i] if type(v) is int and abs(v) != variable and
                         sum(-v in c for c in f) == 1 and
                         not any(-v in f[j] for j in block)]
            if not witnesses:
                raise ValueError('RR10 needs a compatible (i,1) witness in every pivot clause')
        decrease = 0
    elif rule == 'RR11':
        if (len(p),len(n)) not in ((2,1),(1,2)):
            raise ValueError('RR11 needs a (2,1) pivot')
        union = {v for i in block for v in f[i] if type(v) is int and abs(v) != variable}
        if not any(-v in union for v in union):
            raise ValueError('RR11 needs complementary literals in the tails')
        decrease = 1
    else:
        raise ValueError('unknown local resolution rule')
    result = [list(c) for i,c in enumerate(f) if i not in block]
    for i in p:
        for j in n:
            ordinary = {v for v in f[i]+f[j] if type(v) is int and abs(v) != variable}
            tails = {}
            for v in f[i]+f[j]:
                if is_tail(v): tails[v[1]] = tails.get(v[1],False) or v[2]=='nonempty'
            result.append(list(ordinary)+[('tail',t,'nonempty' if flag else 'any')
                                         for t,flag in tails.items()])
    return normalize_formula(result), decrease
