#pragma once

#include "cnf.h"

struct ImportedLemma
{
    std::string rule;
    int pivot_id;
    std::vector<int> branch_vector;
};

std::vector<ImportedLemma> imported_lemma_candidates(
    const std::map<int, FormulaVarStats> &stats);
ProofNode analyze_residual(const CNF &formula, double q);
