#include "xiao_property2.h"
#include "lemmas.h"

namespace {
bool step6_instance(const CNF &formula, int pivot,
                    const std::map<int, FormulaVarStats> &stats)
{
    if (!lemma_degree_scope_is_step6() || MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT)
        return false;
    auto found = stats.find(pivot);
    if (found == stats.end() || found->second.pos_count != 2 ||
        found->second.neg_count != 2) return false;
    for (const auto &[id, s] : stats)
    {
        bool ordinary = s.pos_count == 2 && s.neg_count == 2;
        bool singleton = ((s.pos_count == 3 || s.pos_count == 4) &&
                          s.neg_count == 1 && s.neg_unit_count == 1) ||
                         ((s.neg_count == 3 || s.neg_count == 4) &&
                          s.pos_count == 1 && s.pos_unit_count == 1);
        if (!ordinary && !singleton) return false;
        for (int i : s.pos_indices)
            for (int j : s.neg_indices) if (i == j) return false;
        if (ordinary)
        {
            // Step 4 has already handled every unit clause on a (2,2).
            for (const auto &indices : {s.pos_indices, s.neg_indices})
                for (int index : indices)
                {
                    const auto *clause = formula.clauses[index];
                    int known = 0;
                    for (auto *lit : clause->lits) known += !is_any_unknown_literal(lit);
                    if (known < 2 && clause->tail_atoms.empty()) return false;
                }
        }
    }
    return true;
}
}

bool xiao_step6_context_eligible(const CNF &formula)
{
    const auto stats = analyze_formula(formula);
    for (const auto &[id,s] : stats)
        if (s.pos_count == 2 && s.neg_count == 2)
            return step6_instance(formula,id,stats);
    return false;
}

std::array<bool, 2> xiao_property2_sides(const CNF &formula, int pivot)
{
    std::array<bool, 2> result = {false, false};
    const auto stats = analyze_formula(formula);
    if (!step6_instance(formula, pivot, stats)) return result;
    auto found = stats.find(pivot);
    // x=1 deletes C1,C2, so the witness is in C1 union C2; x=0 uses D1,D2.
    for (int side = 0; side < 2; ++side)
    {
        const auto &indices = side == 0 ? found->second.pos_indices : found->second.neg_indices;
        for (int index : indices)
            for (auto *lit : formula.clauses[index]->lits)
                if (!is_any_unknown_literal(lit) && lit->id != pivot)
                {
                    const auto &s = stats.at(lit->id);
                    if (s.pos_count == 2 && s.neg_count == 2) result[side] = true;
                }
    }
    return result;
}

std::array<bool, 2> xiao_property1_sides(const CNF &formula, int pivot)
{
    std::array<bool, 2> result = {false, false};
    const auto stats = analyze_formula(formula);
    if (!step6_instance(formula, pivot, stats)) return result;
    const auto scope = lemma_current_degree_scope();
    const auto &s = stats.at(pivot);
    for (int side = 0; side < 2; ++side)
    {
        bool valid = true;
        for (int index : side == 0 ? s.pos_indices : s.neg_indices)
        {
            const auto *clause = formula.clauses[index];
            for (const auto *lit : clause->lits)
            {
                if (is_any_unknown_literal(lit) || lit->id == pivot) continue;
                const auto &t = stats.at(lit->id);
                bool singleton31 = !lit->inv
                    ? t.pos_count == 3 && t.neg_count == 1 && t.neg_unit_count == 1
                    : t.neg_count == 3 && t.pos_count == 1 && t.pos_unit_count == 1;
                valid &= singleton31;
            }
            for (const auto &[tail, flag] : clause->tail_atoms)
                for (const auto &degree : scope)
                {
                    if (degree == std::array<int, 3>{3, 1, 1}) continue;
                    bool excluded = false;
                    auto it = formula.tail_exclusions.find(tail);
                    if (it != formula.tail_exclusions.end())
                        for (const auto &d : it->second)
                            excluded |= d[0] == degree[0] && d[1] == degree[1] &&
                                        (!d[2] || degree[2]);
                    valid &= excluded;
                }
        }
        result[side] = valid;
    }
    return result;
}
