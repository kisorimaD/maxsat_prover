#include "cnf.h"

#include <algorithm>
#include <map>
#include <set>
#include <tuple>

using namespace std;

namespace
{
CNF *clone_cnf(const CNF &source)
{
    CNF *copy = new CNF();
    for (Clause *clause : source.clauses)
        copy->clauses.push_back(new Clause(*clause));
    return copy;
}

vector<Literal *> clause_tail(Clause *clause, int excluded_var,
                              const Literal *excluded_literal = nullptr)
{
    vector<Literal *> result;
    for (Literal *lit : clause->lits)
    {
        if (lit->id == excluded_var)
            continue;
        if (excluded_literal && lit->id == excluded_literal->id &&
            lit->inv == excluded_literal->inv)
            continue;
        result.push_back(lit);
    }
    return result;
}

void append_merged_clause(CNF *target,
                          const vector<vector<Literal *>> &parts,
                          const vector<Clause *> &sources = {})
{
    vector<Literal *> merged;
    for (const auto &part : parts)
        merged.insert(merged.end(), part.begin(), part.end());
    map<int, bool> tails;
    for (Clause *source : sources)
        for (auto const &[id, nonempty] : source->tail_atoms)
            tails[id] = tails[id] || nonempty;
    target->clauses.push_back(new Clause(merged, tails));
}

CNF *copy_without(const CNF &source, const set<int> &removed)
{
    CNF *result = new CNF();
    for (int i = 0; i < (int)source.clauses.size(); ++i)
        if (!removed.count(i))
            result->clauses.push_back(new Clause(*source.clauses[i]));
    return result;
}

bool exact_complementary_pair(Clause *positive, Clause *negative,
                              int pivot)
{
    set<pair<int, bool>> positive_tail;
    set<pair<int, bool>> negative_tail;
    bool has_positive = false;
    bool has_negative = false;

    for (Literal *lit : positive->lits)
    {
        if (is_any_unknown_literal(lit)) return false;
        if (lit->id == pivot && !lit->inv)
            has_positive = true;
        else
            positive_tail.insert({lit->id, lit->inv});
    }
    for (Literal *lit : negative->lits)
    {
        if (is_any_unknown_literal(lit)) return false;
        if (lit->id == pivot && lit->inv)
            has_negative = true;
        else
            negative_tail.insert({lit->id, lit->inv});
    }
    return has_positive && has_negative && positive_tail == negative_tail;
}

struct LitKey
{
    int id;
    bool inv;
};

LitKey complement(LitKey lit) { return {lit.id, !lit.inv}; }

bool contains(Clause *clause, LitKey wanted)
{
    for (Literal *lit : clause->lits)
        if (lit->id == wanted.id && lit->inv == wanted.inv)
            return true;
    return false;
}

vector<int> occurrences(const CNF &cnf, LitKey wanted)
{
    vector<int> result;
    for (int i = 0; i < (int)cnf.clauses.size(); ++i)
        if (contains(cnf.clauses[i], wanted))
            result.push_back(i);
    return result;
}

bool dominates(const CNF &cnf, LitKey dominator, LitKey dominated)
{
    vector<int> dominated_occurrences = occurrences(cnf, dominated);
    if (dominated_occurrences.empty())
        return false;
    for (int idx : dominated_occurrences)
        if (!contains(cnf.clauses[idx], dominator))
            return false;
    return true;
}

ReductionStep apply_rr1(const CNF &cnf)
{
    for (int idx = 0; idx < (int)cnf.clauses.size(); ++idx)
    {
        Clause *clause = cnf.clauses[idx];
        for (Literal *lit : clause->lits)
        {
            if (is_any_unknown_literal(lit) ||
                !contains(clause, {lit->id, !lit->inv}))
                continue;
            CNF *reduced = copy_without(cnf, {idx});
            return {true, "RR1", lit->id, 1, {idx}, reduced};
        }
    }
    return {};
}

ReductionStep apply_rr3(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[id, st] : stats)
    {
        bool set_true = st.pos_count > 0 &&
                        st.pos_unit_count >= st.neg_count;
        bool set_false = st.neg_count > 0 &&
                         st.neg_unit_count >= st.pos_count;
        if (!set_true && !set_false)
            continue;

        bool value = set_true;
        CNF *reduced = new CNF();
        for (Clause *clause : cnf.clauses)
        {
            bool satisfied = false;
            vector<Literal *> remaining;
            for (Literal *lit : clause->lits)
            {
                if (lit->id != id)
                {
                    remaining.push_back(lit);
                    continue;
                }
                if (value != lit->inv)
                {
                    satisfied = true;
                    break;
                }
                // The literal is false and is removed from the clause.
            }
            if (!satisfied)
                reduced->clauses.push_back(new Clause(remaining,
                                                       clause->tail_atoms));
        }

        int decrease = (int)cnf.clauses.size() - (int)reduced->clauses.size();
        int promised = value ? st.pos_count : st.neg_count;
        if (decrease < promised)
        {
            destroy_cnf(reduced);
            continue;
        }
        return {true, "RR3", id, decrease, {}, reduced};
    }
    return {};
}

ReductionStep apply_rr2(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[id, st] : stats)
    {
        if (st.pos_count != 1 || st.neg_count != 1)
            continue;

        int pos_idx = st.pos_indices[0];
        int neg_idx = st.neg_indices[0];
        if (pos_idx == neg_idx)
            continue;
        CNF *reduced = copy_without(cnf, {pos_idx, neg_idx});
        append_merged_clause(reduced,
                             {clause_tail(cnf.clauses[pos_idx], id),
                              clause_tail(cnf.clauses[neg_idx], id)},
                             {cnf.clauses[pos_idx], cnf.clauses[neg_idx]});
        int decrease = (int)cnf.clauses.size() - (int)reduced->clauses.size();
        if (decrease < 1)
        {
            destroy_cnf(reduced);
            continue;
        }
        return {true, "RR2", id, decrease, {pos_idx, neg_idx}, reduced};
    }
    return {};
}

ReductionStep apply_rr4(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[id, st] : stats)
    {
        for (int pos_idx : st.pos_indices)
        {
            for (int neg_idx : st.neg_indices)
            {
                if (pos_idx == neg_idx)
                    continue;
                if (!exact_complementary_pair(cnf.clauses[pos_idx],
                                              cnf.clauses[neg_idx], id))
                    continue;

                CNF *reduced = copy_without(cnf, {pos_idx, neg_idx});
                append_merged_clause(reduced,
                                     {clause_tail(cnf.clauses[pos_idx], id)},
                                     {cnf.clauses[pos_idx]});
                int decrease = (int)cnf.clauses.size() -
                               (int)reduced->clauses.size();
                if (decrease < 1)
                {
                    destroy_cnf(reduced);
                    continue;
                }
                return {true, "RR4", id, decrease,
                        {pos_idx, neg_idx}, reduced};
            }
        }
    }
    return {};
}

ReductionStep apply_rr5(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[id, st] : stats)
    {
        for (int orientation = 0; orientation < 2; ++orientation)
        {
            bool dominant_positive = orientation == 0;
            const vector<int> &dominant = dominant_positive
                                               ? st.pos_indices : st.neg_indices;
            const vector<int> &minority = dominant_positive
                                               ? st.neg_indices : st.pos_indices;
            if (dominant.size() != 2 || minority.size() != 1)
                continue;

            for (int xy_idx : dominant)
            {
                Clause *xy_clause = cnf.clauses[xy_idx];
                if (xy_clause->lits.size() != 2)
                    continue;
                Literal *y = nullptr;
                bool exact_two_clause = true;
                for (Literal *lit : xy_clause->lits)
                {
                    if (is_any_unknown_literal(lit))
                    {
                        exact_two_clause = false;
                        break;
                    }
                    if (lit->id != id)
                        y = lit;
                }
                if (!exact_two_clause || !y || y->id == id)
                    continue;

                int xC_idx = dominant[0] == xy_idx ? dominant[1] : dominant[0];
                int nxD_idx = minority[0];
                if (xC_idx == nxD_idx || xy_idx == nxD_idx)
                    continue;

                vector<Literal *> C = clause_tail(cnf.clauses[xC_idx], id);
                vector<Literal *> D = clause_tail(cnf.clauses[nxD_idx], id);
                vector<Literal *> y_part = {y};
                vector<Literal *> not_y = {intern_literal(y->id, !y->inv)};

                CNF *reduced = copy_without(cnf, {xy_idx, xC_idx, nxD_idx});
                append_merged_clause(reduced, {y_part, D},
                                     {cnf.clauses[nxD_idx]});
                append_merged_clause(reduced, {not_y, C, D},
                                     {cnf.clauses[xC_idx], cnf.clauses[nxD_idx]});
                int decrease = (int)cnf.clauses.size() -
                               (int)reduced->clauses.size();
                if (decrease != 1)
                {
                    destroy_cnf(reduced);
                    continue;
                }
                return {true, "RR5", id, decrease,
                        {xy_idx, xC_idx, nxD_idx}, reduced};
            }
        }
    }
    return {};
}

ReductionStep apply_rr6(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[id, st] : stats)
    {
        for (int orientation = 0; orientation < 2; ++orientation)
        {
            bool dominant_positive = orientation == 0;
            int minority_count = dominant_positive ? st.neg_count : st.pos_count;
            int dominant_count = dominant_positive ? st.pos_count : st.neg_count;
            if (minority_count != 1 || dominant_count == 0)
                continue;

            int unique_idx = dominant_positive ? st.neg_indices[0]
                                               : st.pos_indices[0];
            const vector<int> &dominant_indices = dominant_positive
                                                    ? st.pos_indices
                                                    : st.neg_indices;
            if (find(dominant_indices.begin(), dominant_indices.end(), unique_idx) !=
                dominant_indices.end())
                continue;
            Clause *unique_clause = cnf.clauses[unique_idx];

            for (Literal *companion : unique_clause->lits)
            {
                if (is_any_unknown_literal(companion) || companion->id == id)
                    continue;
                auto companion_it = stats.find(companion->id);
                if (companion_it == stats.end())
                    continue;
                const FormulaVarStats &companion_stats = companion_it->second;
                int complement_count = companion->inv
                                         ? companion_stats.pos_count
                                         : companion_stats.neg_count;
                if (complement_count != 1)
                    continue;

                set<int> removed(dominant_indices.begin(), dominant_indices.end());
                removed.insert(unique_idx);
                CNF *reduced = copy_without(cnf, removed);
                vector<Literal *> D = clause_tail(unique_clause, id, companion);
                vector<Literal *> y = {companion};
                for (int dominant_idx : dominant_indices)
                {
                    vector<Literal *> Ci = clause_tail(cnf.clauses[dominant_idx], id);
                    append_merged_clause(reduced, {y, Ci, D},
                                         {cnf.clauses[dominant_idx], unique_clause});
                }

                int decrease = (int)cnf.clauses.size() -
                               (int)reduced->clauses.size();
                if (decrease < 1)
                {
                    destroy_cnf(reduced);
                    continue;
                }
                return {true, "RR6", id, decrease,
                        {unique_idx}, reduced};
            }
        }
    }
    return {};
}

ReductionStep apply_rr7(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[x_id, x_stats] : stats)
    {
        (void)x_stats;
        for (auto const &[y_id, y_stats] : stats)
        {
            (void)y_stats;
            if (x_id == y_id)
                continue;
            for (int x_inv = 0; x_inv < 2; ++x_inv)
            {
                LitKey x = {x_id, (bool)x_inv};
                for (int y_inv = 0; y_inv < 2; ++y_inv)
                {
                    LitKey y = {y_id, (bool)y_inv};
                    if (!dominates(cnf, x, y) ||
                        !dominates(cnf, complement(y), complement(x)))
                        continue;

                    CNF *reduced = new CNF();
                    vector<int> witnesses = occurrences(cnf, y);
                    vector<int> second = occurrences(cnf, complement(x));
                    witnesses.insert(witnesses.end(), second.begin(), second.end());
                    sort(witnesses.begin(), witnesses.end());
                    witnesses.erase(unique(witnesses.begin(), witnesses.end()),
                                    witnesses.end());

                    for (Clause *clause : cnf.clauses)
                    {
                        vector<Literal *> transformed;
                        for (Literal *lit : clause->lits)
                        {
                            if (lit->id != y_id)
                                transformed.push_back(lit);
                            else if (lit->inv == y.inv)
                                transformed.push_back(
                                    intern_literal(x.id, !x.inv));
                            else
                                transformed.push_back(
                                    intern_literal(x.id, x.inv));
                        }
                        reduced->clauses.push_back(new Clause(transformed,
                                                               clause->tail_atoms));
                    }
                    return {true, "RR7", y_id, 0, witnesses, reduced};
                }
            }
        }
    }
    return {};
}

ReductionStep apply_rr8(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[x_id, x_stats] : stats)
    {
        (void)x_stats;
        for (auto const &[y_id, y_stats] : stats)
        {
            (void)y_stats;
            if (x_id == y_id)
                continue;
            for (int x_inv = 0; x_inv < 2; ++x_inv)
            {
                LitKey x = {x_id, (bool)x_inv};
                for (int y_inv = 0; y_inv < 2; ++y_inv)
                {
                    LitKey y = {y_id, (bool)y_inv};
                    if (!dominates(cnf, complement(x), complement(y)))
                        continue;
                    for (int idx = 0; idx < (int)cnf.clauses.size(); ++idx)
                    {
                        if (!contains(cnf.clauses[idx], x) ||
                            !contains(cnf.clauses[idx], y))
                            continue;
                        CNF *reduced = copy_without(cnf, {idx});
                        return {true, "RR8", x_id, 1, {idx}, reduced};
                    }
                }
            }
        }
    }
    return {};
}

bool is_singleton_with_unit_complement(const FormulaVarStats &st, LitKey y)
{
    return y.inv ? st.pos_count == 1 && st.pos_unit_count == 1
                 : st.neg_count == 1 && st.neg_unit_count == 1;
}

ReductionStep apply_rr9(const CNF &cnf,
                        const map<int, FormulaVarStats> &stats)
{
    for (auto const &[x_id, st] : stats)
    {
        if (st.pos_count != 2 || st.neg_count != 2)
            continue;
        for (int orientation = 0; orientation < 2; ++orientation)
        {
            const vector<int> &left = orientation == 0
                                          ? st.pos_indices : st.neg_indices;
            const vector<int> &right = orientation == 0
                                           ? st.neg_indices : st.pos_indices;
            set<int> removed = {left[0], left[1], right[0], right[1]};
            if (removed.size() != 4)
                continue;

            for (Literal *candidate : cnf.clauses[right[0]]->lits)
            {
                if (is_any_unknown_literal(candidate) || candidate->id == x_id)
                    continue;
                LitKey y = {candidate->id, candidate->inv};
                if (!contains(cnf.clauses[right[1]], y))
                    continue;
                auto y_it = stats.find(y.id);
                if (y_it == stats.end() ||
                    !is_singleton_with_unit_complement(y_it->second, y))
                    continue;

                CNF *reduced = copy_without(cnf, removed);
                for (int left_idx : left)
                    for (int right_idx : right)
                        append_merged_clause(
                            reduced,
                            {clause_tail(cnf.clauses[left_idx], x_id),
                             clause_tail(cnf.clauses[right_idx], x_id)},
                            {cnf.clauses[left_idx], cnf.clauses[right_idx]});
                return {true, "RR9", x_id, 0,
                        {left[0], left[1], right[0], right[1]}, reduced};
            }
        }
    }
    return {};
}
} // namespace

ReductionStep apply_named_reduction(const CNF &cnf, const string &rule)
{
    map<int, FormulaVarStats> stats = analyze_formula(cnf);
    if (rule == "RR1") return apply_rr1(cnf);
    if (rule == "RR2") return apply_rr2(cnf, stats);
    if (rule == "RR3") return apply_rr3(cnf, stats);
    if (rule == "RR4") return apply_rr4(cnf, stats);
    if (rule == "RR5") return apply_rr5(cnf, stats);
    if (rule == "RR6") return apply_rr6(cnf, stats);
    if (rule == "RR7") return apply_rr7(cnf, stats);
    if (rule == "RR8") return apply_rr8(cnf, stats);
    if (rule == "RR9") return apply_rr9(cnf, stats);
    return {};
}

ReductionStep apply_first_reduction(const CNF &cnf)
{
    for (int number = 1; number <= 9; ++number)
    {
        ReductionStep step = apply_named_reduction(
            cnf, "RR" + to_string(number));
        if (step.applied)
            return step;
    }
    return {};
}

ReductionFixpoint reduce_to_fixpoint(const CNF &cnf)
{
    ReductionFixpoint result;
    result.cnf = clone_cnf(cnf);

    while (true)
    {
        ReductionStep step = apply_first_reduction(*result.cnf);
        if (!step.applied)
            break;

        if (step.decrease < 0 || !step.cnf)
        {
            if (step.cnf) destroy_cnf(step.cnf);
            break;
        }

        result.total_decrease += step.decrease;
        CNF *next = step.cnf;
        step.cnf = nullptr;
        result.steps.push_back(step);
        destroy_cnf(result.cnf);
        result.cnf = next;
    }

    return result;
}

vector<DirectLemmaResult> find_direct_lemma23_candidates(const CNF &cnf)
{
    map<int, FormulaVarStats> stats = analyze_formula(cnf);
    vector<DirectLemmaResult> candidates;
    vector<int> unit_singletons;

    auto add = [&](const string &rule, int pivot, int second,
                   int local_D, int pos, int neg,
                   const vector<int> &vec)
    {
        DirectLemmaResult candidate;
        candidate.applied = true;
        candidate.rule = rule;
        candidate.pivot_id = pivot;
        candidate.second_pivot_id = second;
        candidate.local_D = local_D;
        candidate.pos_count = pos;
        candidate.neg_count = neg;
        candidate.vec = vec;
        candidate.tau = branching_factor(vec);
        candidates.push_back(candidate);
    };

    for (auto const &[id, st] : stats)
    {
        bool singleton =
            (st.pos_count == 2 && st.neg_count == 1 &&
             st.neg_unit_count == 1) ||
            (st.neg_count == 2 && st.pos_count == 1 &&
             st.pos_unit_count == 1);
        if (singleton)
            unit_singletons.push_back(id);

        // Lemma 3: every variable of total degree three, oriented so that
        // the literal occurring twice is x and the unique occurrence is xbar D.
        if (st.pos_count + st.neg_count == 3 &&
            ((st.pos_count == 2 && st.neg_count == 1) ||
             (st.neg_count == 2 && st.pos_count == 1)))
        {
            int D = st.neg_count == 1 ? st.neg_min_D : st.pos_min_D;
            if (D != 999999)
                add("lemma3", id, -1, D, st.pos_count, st.neg_count,
                    {1, max(8, 7 + 2 * D)});
        }

        // Lemma 2: an (i,1)-literal in either orientation.
        if (st.pos_count > 0 && st.neg_count > 0 &&
            (st.pos_count == 1 || st.neg_count == 1))
        {
            int i = max(st.pos_count, st.neg_count);
            int D = st.neg_count == 1 ? st.neg_min_D : st.pos_min_D;
            if (D != 999999)
                add("lemma2", id, -1, D, st.pos_count, st.neg_count,
                    {i, 1 + 2 * D});
        }
    }

    // The Step 5.5 cascade already used by the group search: after applying
    // Lemma 3 to one unit (2,1)-singleton, the second one remains available.
    if (unit_singletons.size() >= 2)
    {
        int first = unit_singletons[0];
        int second = unit_singletons[1];
        const FormulaVarStats &st = stats.at(first);
        int D = st.neg_count == 1 ? st.neg_min_D : st.pos_min_D;
        add("double_lemma3", first, second, D,
            st.pos_count, st.neg_count, {2, 9, 8});
    }

    return candidates;
}

DirectLemmaResult find_best_direct_lemma23(const CNF &cnf)
{
    DirectLemmaResult best;
    for (const DirectLemmaResult &candidate :
         find_direct_lemma23_candidates(cnf))
    {
        bool strictly_better = !best.applied ||
                               candidate.tau < best.tau - 1e-12;
        bool step55_tie = best.applied &&
                          candidate.rule == "double_lemma3" &&
                          best.rule == "lemma3" &&
                          abs(candidate.tau - best.tau) <= 1e-12;
        if (strictly_better || step55_tie)
            best = candidate;
    }
    return best;
}
