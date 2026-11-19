#include "residual_search.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <stdexcept>

using namespace std;

vector<ImportedLemma> imported_lemma_candidates(const map<int, FormulaVarStats> &stats)
{
    vector<ImportedLemma> candidates;
    int first_singleton = -1;
    int singleton_count = 0;

    for (const auto &[id, st] : stats)
    {
        int i = max(st.pos_count, st.neg_count);
        int j = min(st.pos_count, st.neg_count);
        if (j != 1) continue;

        int D = st.neg_count == 1 ? st.neg_min_D : st.pos_min_D;
        if (i == 2)
        {
            int minority_units = st.neg_count == 1 ? st.neg_unit_count : st.pos_unit_count;
            if (minority_units == 1)
            {
                if (singleton_count == 0) first_singleton = id;
                ++singleton_count;
            }
            if (D != 999999)
                candidates.push_back({"lemma3", id, {1, max(8, 7 + 2 * D)}});
        }
        if (D != 999999)
            candidates.push_back({"lemma2", id, {i, 1 + 2 * D}});
    }

    // In Step 5.5 the first resolution child preserves the second singleton.
    // The second reduction case (8,2) is covered by (2,9,8).
    if (singleton_count >= 2)
        candidates.push_back({"double_lemma3", first_singleton, {2, 9, 8}});

    // Lemma 4 requires j-1 unit clauses on the side with i occurrences.
    for (const auto &[id, st] : stats)
    {
        if (st.pos_count >= st.neg_count && st.neg_count >= 2 &&
            st.pos_unit_count >= st.neg_count - 1)
            candidates.push_back({"lemma4", id, {st.pos_count, 2 * st.neg_count + 1}});
        if (st.neg_count >= st.pos_count && st.pos_count >= 2 &&
            st.neg_unit_count >= st.pos_count - 1)
            candidates.push_back({"lemma4", id, {st.neg_count, 2 * st.pos_count + 1}});
    }

    return candidates;
}

namespace {
using OwnedCNF = unique_ptr<CNF, decltype(&destroy_cnf)>;

ProofNode call_on(const CNF &formula)
{
    ProofNode call({0});
    call.formula_snapshot = formula.get_cert_snapshot();
    return call;
}

pair<int, OwnedCNF> apply_assignment(const CNF &formula, int variable, bool value)
{
    OwnedCNF residual(new CNF(), destroy_cnf);
    int decrease = 0;
    for (Clause *clause : formula.clauses)
    {
        bool satisfied = false;
        vector<Literal *> remaining;
        for (Literal *literal : clause->lits)
        {
            if (is_any_unknown_literal(literal) || literal->id != variable)
                remaining.push_back(literal);
            else if (value != literal->inv)
            {
                satisfied = true;
                break;
            }
        }

        if (satisfied || remaining.empty())
            ++decrease;
        else if (!all_of(remaining.begin(), remaining.end(), is_any_unknown_literal))
            residual->clauses.push_back(new Clause(remaining, clause->tail_atoms));
        // A tail-only clause leaves the local formula without decreasing m.
    }
    return {decrease, move(residual)};
}

ProofNode choose_residual_continuation(const CNF &formula, double q)
{
    ProofNode best = call_on(formula);
    long double best_weight = numeric_limits<long double>::infinity();
    const auto stats = analyze_formula(formula);
    if (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
    {
        for (const ImportedLemma &lemma : imported_lemma_candidates(stats))
        {
            vector<int> bound = reduction_or_branch_bound(lemma.branch_vector, q);
            long double weight = branching_weight(bound, q);
            bool step55_tie = weight == best_weight && best.rule == "lemma3" &&
                              lemma.rule == "double_lemma3";
            if (weight < best_weight || step55_tie)
            {
                best_weight = weight;
                best.vec = move(bound);
                best.tau = branching_factor(best.vec);
                best.rule = lemma.rule;
                best.pivot_id = lemma.pivot_id;
                best.assumption_branch_vector = lemma.branch_vector;
            }
        }
    }

    // Step 5.1: the minority literal of a (3,2)-variable has a unit clause.
    for (const auto &[id, st] : stats)
    {
        bool positive_dominant = st.pos_count == 3 && st.neg_count == 2 && st.neg_unit_count >= 1;
        bool negative_dominant = st.neg_count == 3 && st.pos_count == 2 && st.pos_unit_count >= 1;
        if (!positive_dominant && !negative_dominant) continue;

        auto [true_decrease, true_residual] = apply_assignment(formula, id, true);
        auto [false_decrease, false_residual] = apply_assignment(formula, id, false);
        ProofNode candidate({true_decrease, false_decrease});
        long double weight = branching_weight(candidate.vec, q);
        if (weight < best_weight)
        {
            best_weight = weight;
            candidate.type = "branch";
            candidate.pivot_id = id;
            candidate.formula_snapshot = best.formula_snapshot;
            candidate.reduced_cnt_true = true_decrease;
            candidate.reduced_cnt_false = false_decrease;
            candidate.offset_true = st.pos_count;
            candidate.offset_false = st.neg_count;
            candidate.children = {call_on(*true_residual), call_on(*false_residual)};
            best = move(candidate);
        }
    }
    return best;
}
} // namespace

ProofNode analyze_residual(const CNF &formula, double q)
{
    if (!isfinite(q) || q <= 1.0)
        throw invalid_argument("invalid strategy search target");

    ReductionFixpoint reduced = reduce_to_fixpoint(formula);
    OwnedCNF owner(reduced.cnf, destroy_cnf);
    ProofNode child = reduced.total_decrease == 0
                          ? choose_residual_continuation(*owner, q)
                          : call_on(*owner);
    for (auto it = reduced.steps.rbegin(); it != reduced.steps.rend(); ++it)
    {
        ProofNode parent;
        parent.type = "reduction";
        parent.rule = it->rule;
        parent.pivot_id = it->pivot_id;
        parent.formula_snapshot = it->formula_snapshot;
        parent.vec = child.vec;
        for (int &decrease : parent.vec) decrease += it->decrease;
        parent.tau = branching_factor(parent.vec);
        parent.children.push_back(move(child));
        child = move(parent);
    }
    return child;
}
