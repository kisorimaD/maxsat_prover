#include "cnf.h"
#include <algorithm>
#include <map>
#include <vector>
#include <set>

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
            if (new_lits_vec.size() == 1 && is_any_unknown_literal(new_lits_vec[0]))
                continue;

            Clause *new_c = new Clause(new_lits_vec);
            new_cnf->clauses.push_back(new_c);
        }
    }
    return {satisfied_cnt, new_cnf};
}

// std::vector<std::vector<int>> CNF::get_snapshot() {
//     std::vector<std::vector<int>> snap;
//     for (Clause* c : clauses) {
//         std::vector<int> cl_snap;
//         for (Literal* l : c->lits) {
//             if (is_any_unknown_literal(l)) cl_snap.push_back(l->id);
//             else cl_snap.push_back((l->inv ? -1 : 1) * l->id);
//         }
//         snap.push_back(cl_snap);
//     }
//     return snap;
// }

ProofNode CNF::xiao_branch(int depth, std::string first_var)
{
    // The search considers every actual pivot.  In particular, if a good
    // (3,2)-variable exists, it must be selected as that pivot; its bound
    // cannot be transferred to a different distinguished variable.
    (void)first_var;

    double granted = 100.0;
    ProofNode granted_node({0});
    granted_node.tau = 100.0;
    granted_node.formula_snapshot = this->get_snapshot();

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
            child_node = reduction.cnf->xiao_branch(depth, first_var);
        }
        else
        {
            child_node = ProofNode({reduction.decrease});
            child_node.formula_snapshot = reduction.cnf->get_snapshot();
        }

        ProofNode parent;
        parent.type = "reduction";
        parent.rule = reduction.rule;
        parent.pivot_id = reduction.pivot_id;
        parent.vec = child_node.vec;
        parent.tau = child_node.tau;
        parent.formula_snapshot = this->get_snapshot();
        parent.rr_witness_clauses = reduction.witness_clauses;
        parent.children.push_back(child_node);
        destroy_cnf(reduction.cnf);
        return parent;
    }

    // Lemmas 2 and 3 apply to arbitrary child formulas, not only to affine
    // residuals produced by group branching.  Keeping this before the depth
    // cutoff is essential: a depth-1 branch must see the lemma in its child.
    DirectLemmaResult direct_lemma = find_best_direct_lemma23(*this);
    if (direct_lemma.applied && direct_lemma.tau < granted)
    {
        granted = direct_lemma.tau;
        granted_node.vec = direct_lemma.vec;
        granted_node.tau = direct_lemma.tau;
        granted_node.rule = direct_lemma.rule;
        granted_node.pivot_id = direct_lemma.pivot_id;
        granted_node.formula_snapshot = this->get_snapshot();
    }

    // Step 4 / Lemma 4.
    // For an (i,j)-literal a, the unit clauses must contain a itself
    // (the side with i occurrences), not its complement.  The resulting
    // branching vector is (i, 2j+1), where i >= j >= 2.
    for (auto const &[id, s] : stats)
    {
        auto try_lemma4 = [&](int i, int j, int unit_count)
        {
            if (i >= j && j >= 2 && unit_count >= j - 1)
            {
                vector<int> step4_branch = {i, 2 * j + 1};
                double f = branching_factor(step4_branch);
                if (f < granted)
                {
                    granted = f;
                    granted_node.vec = step4_branch;
                    granted_node.tau = f;
                    granted_node.formula_snapshot = this->get_snapshot();
                }
            }
        };

        // a is the positive literal.
        try_lemma4(s.pos_count, s.neg_count, s.pos_unit_count);
        // a is the negative literal.
        try_lemma4(s.neg_count, s.pos_count, s.neg_unit_count);
    }

    // Step 5.1.  This is a different case from Lemma 4: a unit clause
    // contains the minority literal of a (3,2)-variable.  Direct branching
    // removes the unit clause as well in the dominant branch and gives
    // (4,2), not (5,2).
    for (auto const &[id, s] : stats)
    {
        bool has_positive_dominant_case =
            s.pos_count == 3 && s.neg_count == 2 && s.neg_unit_count >= 1;
        bool has_negative_dominant_case =
            s.neg_count == 3 && s.pos_count == 2 && s.pos_unit_count >= 1;

        if (has_positive_dominant_case || has_negative_dominant_case)
        {
            vector<int> step51_branch = {4, 2};
            double f = branching_factor(step51_branch);
            if (f < granted)
            {
                granted = f;
                granted_node.vec = step51_branch;
                granted_node.tau = f;
                granted_node.formula_snapshot = this->get_snapshot();
            }
        }
    }

    if (depth == 0) return granted_node;

    // --- Branching ---
    ProofNode best_node;
    double min_tau = 1e18;
    bool any_var_processed = false;

    for (auto const &[var_id, s] : stats)
    {
        // Ветвь 1: x = 1
        auto [reduced_cnt1, new_cnf1] = apply_xiao_assignment(this, var_id, true);
        ProofNode child1_res = new_cnf1->xiao_branch(depth - 1, "");
        ProofNode stop1_res({0});
        stop1_res.formula_snapshot = new_cnf1->get_snapshot();

        // Ветвь 2: x = 0
        auto [reduced_cnt0, new_cnf0] = apply_xiao_assignment(this, var_id, false);
        ProofNode child0_res = new_cnf0->xiao_branch(depth - 1, "");
        ProofNode stop0_res({0});
        stop0_res.formula_snapshot = new_cnf0->get_snapshot();

        ProofNode f_nodes[2] = {child1_res, stop1_res};
        ProofNode s_nodes[2] = {child0_res, stop0_res};

        for (int i = 0; i < 2; ++i)
        {
            for (int j = 0; j < 2; ++j)
            {
                vector<int> current_branching;
                for (int el : f_nodes[i].vec) current_branching.push_back(reduced_cnt1 + el);
                for (int el : s_nodes[j].vec) current_branching.push_back(reduced_cnt0 + el);

                double current_tau = branching_factor(current_branching);

                if (!any_var_processed || current_tau < min_tau)
                {
                    min_tau = current_tau;
                    any_var_processed = true;
                    
                    best_node.type = "branch";
                    best_node.pivot_id = var_id;
                    best_node.vec = current_branching;
                    best_node.tau = current_tau;
                    best_node.children = {f_nodes[i], s_nodes[j]};
                    best_node.reduced_cnt_true = reduced_cnt1;
                    best_node.reduced_cnt_false = reduced_cnt0;
                }
            }
        }

        destroy_cnf(new_cnf1);
        destroy_cnf(new_cnf0);
    }

    if (!any_var_processed) return ProofNode({0});

    std::sort(best_node.vec.begin(), best_node.vec.end(), std::greater<int>());

    if (best_node.tau > granted) {
        return granted_node;
    }

    best_node.formula_snapshot = this->get_snapshot();

    return best_node;
}
