"""Exact variable-eliminating reductions eligible for a global solver restart."""
from .formula import normalize_formula,variables,tail_ids
from .local_resolution import resolution_result


def validate_restart(node):
    if set(node)!={'kind','formula','variable','rule','proof'}:
        raise ValueError('invalid restart fields')
    child=node['proof']
    if not isinstance(child,dict) or set(child)!={'kind','formula'} or child['kind']!='call':
        raise ValueError('restart requires an opaque global continuation')
    parent=normalize_formula(node['formula']);residual=normalize_formula(child['formula'])
    variable=node['variable'];rule=node['rule']
    if type(variable) is not int or variable<2:
        raise ValueError('restart requires an ordinary eliminated variable')
    before=set(variables(parent));after=set(variables(residual))
    if variable not in before or variable in after or not after<before:
        raise ValueError('restart must eliminate a real ordinary variable without introducing any')
    if len(residual)!=len(parent) or not set(tail_ids(residual))<=set(tail_ids(parent)):
        raise ValueError('zero-cost restart must preserve clause count and introduce no tails')
    if rule in ('RR9','RR10'):
        expected,decrease=resolution_result(node['formula'],variable,rule)
        if decrease!=0 or expected!=residual:raise ValueError('incorrect restart resolution residual')
    elif rule=='RR7':
        # Native RR7 eliminates y=variable via y_lit := not x_lit.
        matched=False
        def occurrences(literal):return [c for c in parent if literal in c]
        def dominates(a,b):return bool(occurrences(b)) and all(a in c for c in occurrences(b))
        for x in before-{variable}:
            for a in (x,-x):
                for b in (variable,-variable):
                    if not dominates(a,b) or not dominates(-b,-a):continue
                    candidate=[]
                    for clause in parent:
                        candidate.append(list({-a if v==b else a if v==-b else v for v in clause}))
                    if normalize_formula(candidate)==residual:matched=True
        if not matched:raise ValueError('incorrect RR7 dominance or residual')
    else:raise ValueError('unsupported restart rule')
    return sorted(before-after)


def progressing(node, paid=0, eliminated=0):
    """All calls pay m; a zero-cost restart strictly reduces actual n.

    Forgetting/exposing a variable changes its visibility, not actual n.
    Semantic rewrites can introduce ordinary variables, so their variable
    balance must also be charged before crediting an eventual restart.
    """
    kind=node['kind']
    def variable_drop(parent,child):
        return len(variables(normalize_formula(parent)))-len(variables(normalize_formula(child)))
    if kind=='call':return paid>0
    if kind=='restart':
        return paid>0 or (paid==0 and eliminated+variable_drop(node['formula'],node['proof']['formula'])>0)
    if kind=='assumption':return all(paid+d>0 for d in node['vector'])
    if kind=='lemma3_split':
        return paid+1>0 and paid+node['long_decrease']>0 and progressing(node['proof'],paid+1,eliminated+variable_drop(node['formula'],node['proof']['formula']))
    if kind in ('strategy','local_context'):return progressing(node['proof'],paid,eliminated)
    if kind=='refine':return all(progressing(c,paid,eliminated) for c in node['children'])
    if kind=='local_resolution':
        child=node['proof']
        return progressing(child,paid+len(node['formula'])-len(child['formula']),
                           eliminated+variable_drop(node['formula'],child['formula']))
    if kind=='decompose':
        return all(progressing(a['proof'],paid+a['decrease'],
                               eliminated+variable_drop(node['formula'],a['formula'])) for a in node['alternatives'])
    if kind in ('xiao_property1_branch','xiao_property2_branch'):
        from .formula import assignment_residual
        properties=node['properties'] if kind=='xiao_property1_branch' else [2 if p else 0 for p in node['imported_sides']]
        for i,(imported,child) in enumerate(zip(properties,node['children'])):
            if imported:
                if not all(paid+d>0 for d in ((18,11,11,4) if imported==1 else (11,3))):return False
            else:
                _,_,decrease=assignment_residual(normalize_formula(node['formula']),node['variable'],i==0)
                if not progressing(child,paid+decrease,eliminated+variable_drop(node['formula'],child['formula'])):return False
        return True
    return False
