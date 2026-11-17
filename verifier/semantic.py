from itertools import product
from functools import lru_cache

import numpy as np

from .formula import check_formula_size, is_tail, variables, normalize_formula


def optimum_vector(formula, boundary_ids):
    """OPT for every boundary valuation, computed independently and exactly."""
    formula = normalize_formula(formula)
    boundary_ids = tuple(boundary_ids)
    if len(boundary_ids) > 14:
        return _compute_optimum_vector(formula,boundary_ids)
    # Preserve the order of boundary bits, while removing irrelevant names.
    # A saved RR proof is otherwise recomputed after every alpha-renaming.
    ordinary = {v:i+2 for i,v in enumerate(variables(formula))}
    boundary = {v:i for i,v in enumerate(boundary_ids)}
    renamed = normalize_formula([
        [('tail',boundary[v[1]],v[2]) if is_tail(v)
         else ordinary[abs(v)] * (1 if v>0 else -1) for v in clause]
        for clause in formula])
    return _cached_optimum_vector(renamed,len(boundary_ids)).copy()


@lru_cache(maxsize=2048)
def _cached_optimum_vector(formula, boundary_count):
    # At most 64 MiB of int16 payload (2048 * 2^14 * 2 bytes).
    result = _compute_optimum_vector(formula,tuple(range(boundary_count)))
    result.flags.writeable = False
    return result


def _compute_optimum_vector(formula, boundary_ids):
    check_formula_size(formula)
    positions = {tail_id: index for index, tail_id in enumerate(boundary_ids)}
    count = 1 << len(boundary_ids)
    boundary_values = np.arange(count, dtype=np.uint64)
    best = np.zeros(count, dtype=np.int16)
    ids = variables(formula)

    for values in product((False, True), repeat=len(ids)):
        assignment = dict(zip(ids, values))
        score = np.zeros(count, dtype=np.int16)
        for clause in formula:
            explicit_true = False
            tail_mask = 0
            for literal in clause:
                if is_tail(literal):
                    tail_mask |= 1 << positions[literal[1]]
                elif assignment[abs(literal)] != (literal < 0):
                    explicit_true = True
                    break
            if explicit_true:
                score += 1
            elif tail_mask:
                score += (boundary_values & tail_mask) != 0
        best = np.maximum(best, score)
    return best
