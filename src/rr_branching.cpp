#include "cnf.h"
#include "strategy_cache.h"
#include <algorithm>
#include <map>
#include <vector>
#include <set>
#include <limits>

using namespace std;

pair<int, CNF *> apply_xiao_assignment(CNF *original, int var_id, bool val_to_set)
{
    CNF *new_cnf = new CNF();
    int satisfied_cnt = 0;

    for (Clause *c : original->clauses)
    {
        bool satisfied = false;
        vector<Literal *> new_lits_vec;

        for (Literal *l : c->lits)
        {
            if (l == &UNKNOWN_LITERAL)
            {
                new_lits_vec.push_back(l);
                continue;
            }

            if (l->id == var_id)
            {
                bool is_lit_true = (val_to_set && !l->inv) || (!val_to_set && l->inv);
                if (is_lit_true)
                {
                    satisfied = true;
                    break;
                }
            }
            else
            {
                new_lits_vec.push_back(l);
            }
        }

        if (satisfied || new_lits_vec.empty())
        {
            satisfied_cnt++;
        }
        else
        {
            if (all_of(new_lits_vec.begin(), new_lits_vec.end(), is_any_unknown_literal))
                continue;

            Clause *new_c = new Clause(new_lits_vec, c->tail_atoms);
            new_cnf->clauses.push_back(new_c);
        }
    }
    return {satisfied_cnt, new_cnf};
}

ProofNode CNF::xiao_branch(int depth, double q)
{
    return cached_strategy_search(*this, StrategySearchKind::Variable, depth, q,
                                  [&] { return xiao_branch_uncached(depth, q); });
}

ProofNode CNF::xiao_branch_uncached(int depth, double q)
{
    // The search considers every actual pivot.  In particular, if a good
    // (3,2)-variable exists, it must be selected as that pivot; its bound
    // cannot be transferred to a different distinguished variable.

    long double granted = std::numeric_limits<long double>::infinity();
    ProofNode granted_node({0});
    granted_node.tau = 100.0;
    granted_node.formula_snapshot = this->get_cert_snapshot();

    map<int, FormulaVarStats> stats = analyze_formula(*this);

    ReductionStep reduction = apply_first_reduction(*this);
    if (reduction.applied)
    {
        ProofNode child_node;
        if (reduction.decrease == 0)
        {
            // RR7 and RR9 preserve the number of clauses but eliminate a
            // variable.  Continue on the transformed formula instead of
            // returning the meaningless branching vector (0).
            child_node = reduction.cnf->xiao_branch(depth, q);
        }
        else
        {
            // The reduction edge itself accounts for the decrease.  Its
            // child is a recursive call, not another copy of that decrease.
            child_node = ProofNode({0});
            child_node.tau = 100.0;
            child_node.formula_snapshot = reduction.cnf->get_cert_snapshot();
        }

        ProofNode parent;
        parent.type = "reduction";
        parent.rule = reduction.rule;
        parent.pivot_id = reduction.pivot_id;
        parent.vec = reduction.decrease == 0
                         ? child_node.vec
                         : vector<int>{reduction.decrease};
        parent.tau = reduction.decrease == 0
                         ? child_node.tau
                         : branching_factor(parent.vec);
        parent.formula_snapshot = this->get_cert_snapshot();
        parent.children.push_back(child_node);
        destroy_cnf(reduction.cnf);
        return parent;
    }

    // Lemmas 2 and 3 apply to arbitrary child formulas, not only to affine
    // residuals produced by group branching.  Keeping this before the depth
    // cutoff is essential: a depth-1 branch must see the lemma in its child.
    auto consider_import = [&](const string &rule, int pivot, const vector<int> &branch_vector)
    {
        vector<int> bound = reduction_or_branch_bound(branch_vector, q);
        long double weight = branching_weight(bound, q);
        if (weight < granted)
        {
            granted = weight;
            granted_node = ProofNode(std::move(bound));
            granted_node.rule = rule;
            granted_node.pivot_id = pivot;
            granted_node.formula_snapshot = get_cert_snapshot();
            granted_node.assumption_branch_vector = branch_vector;
        }
    };

    // Step 4 / Lemma 4.
    // For an (i,j)-literal a, the unit clauses must contain a itself
    // (the side with i occurrences), not its complement.  The resulting
    // branching vector is (i, 2j+1), where i >= j >= 2.
    if (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
    {
        DirectLemmaResult direct_lemma = find_best_direct_lemma23(*this, q);
        if (direct_lemma.applied)
            consider_import(direct_lemma.rule, direct_lemma.pivot_id, direct_lemma.vec);

        for (auto const &[id, s] : stats)
        {
            auto try_lemma4 = [&](int i, int j, int unit_count)
            {
                if (i >= j && j >= 2 && unit_count >= j - 1)
                    consider_import("lemma4", id, {i, 2 * j + 1});
            };

            // a is the positive literal.
            try_lemma4(s.pos_count, s.neg_count, s.pos_unit_count);
            // a is the negative literal.
            try_lemma4(s.neg_count, s.pos_count, s.neg_unit_count);
        }
    }

    // Step 5.1.  This is a different case from Lemma 4: a unit clause
    // contains the minority literal of a (3,2)-variable.  Direct branching
    // removes the unit clause as well in the dominant branch and gives
    // (4,2), not (5,2).
    for (auto const &[id, s] : stats)
    {
        bool positive_dominant = s.pos_count == 3 && s.neg_count == 2 && s.neg_unit_count >= 1;
        bool negative_dominant = s.neg_count == 3 && s.pos_count == 2 && s.pos_unit_count >= 1;
        if (!positive_dominant && !negative_dominant) continue;

        auto [true_decrease, true_cnf] = apply_xiao_assignment(this, id, true);
        auto [false_decrease, false_cnf] = apply_xiao_assignment(this, id, false);
        ProofNode candidate({true_decrease, false_decrease});
        candidate.type = "branch";
        candidate.pivot_id = id;
        candidate.formula_snapshot = get_cert_snapshot();
        candidate.reduced_cnt_true = true_decrease;
        candidate.reduced_cnt_false = false_decrease;
        candidate.offset_true = s.pos_count;
        candidate.offset_false = s.neg_count;
        for (CNF *residual : {true_cnf, false_cnf})
        {
            ProofNode call({0});
            call.formula_snapshot = residual->get_cert_snapshot();
            candidate.children.push_back(std::move(call));
            destroy_cnf(residual);
        }
        long double weight = branching_weight(candidate.vec, q);
        if (weight < granted)
        {
            granted = weight;
            granted_node = std::move(candidate);
        }
    }

    if (depth == 0) return granted_node;

    // --- Branching ---
    ProofNode best_node;
    long double min_weight = std::numeric_limits<long double>::infinity();
    bool any_var_processed = false;

    for (auto const &[var_id, s] : stats)
    {
        auto assignment_offset = [&](bool value)
        {
            int result = 0;
            for (Clause *clause : clauses)
                for (Literal *lit : clause->lits)
                    if (!is_any_unknown_literal(lit) && lit->id == var_id &&
                        value != lit->inv)
                    {
                        ++result;
                        break;
                    }
            return result;
        };
        // Ветвь 1: x = 1
        auto [reduced_cnt1, new_cnf1] = apply_xiao_assignment(this, var_id, true);
        ProofNode child1_res = new_cnf1->xiao_branch(depth - 1, q);
        ProofNode stop1_res({0});
        stop1_res.formula_snapshot = new_cnf1->get_cert_snapshot();

        // Ветвь 2: x = 0
        auto [reduced_cnt0, new_cnf0] = apply_xiao_assignment(this, var_id, false);
        ProofNode child0_res = new_cnf0->xiao_branch(depth - 1, q);
        ProofNode stop0_res({0});
        stop0_res.formula_snapshot = new_cnf0->get_cert_snapshot();

        // Contributions are additive at fixed q: each child independently
        // chooses its continuation or a call (whose weight is one).
        ProofNode selected1 = branching_weight(child1_res.vec, q) < 1.0L
                                  ? child1_res : stop1_res;
        ProofNode selected0 = branching_weight(child0_res.vec, q) < 1.0L
                                  ? child0_res : stop0_res;
        vector<int> current_branching;
        for (int el : selected1.vec) current_branching.push_back(reduced_cnt1 + el);
        for (int el : selected0.vec) current_branching.push_back(reduced_cnt0 + el);
        long double current_weight = branching_weight(current_branching, q);
        if (!any_var_processed || current_weight < min_weight)
        {
            min_weight = current_weight;
            any_var_processed = true;
            best_node.type = "branch";
            best_node.pivot_id = var_id;
            best_node.vec = move(current_branching);
            best_node.tau = branching_factor(best_node.vec);
            best_node.children = {move(selected1), move(selected0)};
            best_node.reduced_cnt_true = reduced_cnt1;
            best_node.reduced_cnt_false = reduced_cnt0;
            best_node.offset_true = assignment_offset(true);
            best_node.offset_false = assignment_offset(false);
        }

        destroy_cnf(new_cnf1);
        destroy_cnf(new_cnf0);
    }

    if (!any_var_processed) return granted_node;

    std::sort(best_node.vec.begin(), best_node.vec.end(), std::greater<int>());

    if (min_weight > granted) {
        return granted_node;
    }

    best_node.formula_snapshot = this->get_cert_snapshot();

    return best_node;
}
