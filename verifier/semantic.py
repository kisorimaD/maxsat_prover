from itertools import product

import numpy as np

from .formula import is_tail, variables


def optimum_vector(formula, boundary_ids):
    """OPT for every boundary valuation, computed independently and exactly."""
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
