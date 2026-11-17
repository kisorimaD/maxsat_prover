#include "cnf.h"
#include "strategy_cache.h"
#include "lemmas.h"
#include "xiao_property2.h"
#include <algorithm>
#include <map>
#include <vector>
#include <set>
#include <limits>

using namespace std;

namespace {
struct ResolutionContext {
    bool previous = MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT;
    ResolutionContext() { MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT = true; }
    ~ResolutionContext() { MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT = previous; }
};
}

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
            // A boundary-only clause leaves the local neighbourhood but stays
            // in the global instance. Mixed '?' / '?+' markers need the same
            // treatment as a single marker, without any additional decrease.
            if (all_of(new_lits_vec.begin(), new_lits_vec.end(), is_any_unknown_literal))
                continue;

            Clause *new_c = new Clause(new_lits_vec, c->tail_atoms);
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

ProofNode CNF::xiao_branch(int depth, std::string first_var, double q)
{
    (void)first_var;
    return cached_strategy_search(*this, StrategySearchKind::Variable, depth, q,
                                  [&] {
        bool context = MaxSATSettings.ALLOW_XIAO_PROPERTY2;
        bool context1 = MaxSATSettings.ALLOW_XIAO_PROPERTY1;
        DisableXiaoProperty2 no_inherited_step6_premise;
        return xiao_branch_uncached(depth, q, context, context1);
    });
}

ProofNode CNF::xiao_branch_uncached(int depth, double q, bool property2_context, bool property1_context)
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
        ProofNode restart;
        if (MaxSATSettings.ALLOW_POLYNOMIAL_RESTARTS) restart=polynomial_restart(*this,reduction);
        // These resolutions can duplicate boundary literals. Do not reuse
        // degree-conditional saved lemmas under the old hidden-degree scope.
        std::unique_ptr<ResolutionContext> resolution_scope;
        if (reduction.rule == "RR10" || reduction.rule == "RR11")
            resolution_scope = std::make_unique<ResolutionContext>();
        ProofNode child_node;
        if (reduction.decrease == 0)
        {
            // RR7 and RR9 preserve the number of clauses but eliminate a
            // variable.  Continue on the transformed formula instead of
            // returning the meaningless branching vector (0).
            child_node = reduction.cnf->xiao_branch(depth, "", q);
        }
        else
        {
            // The edge accounts for the decrease. A call is the fallback;
            // inside the explicit resolution arm the budget may permit a
            // further improving continuation.
            child_node = ProofNode({0});
            child_node.tau = 100.0;
            child_node.formula_snapshot = reduction.cnf->get_cert_snapshot();
            if (depth > 0 && MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT)
            {
                auto continuation = reduction.cnf->xiao_branch(depth - 1, "", q);
                if (branching_weight(continuation.vec, q) < 1.0L)
                    child_node = std::move(continuation);
            }
        }

        ProofNode parent;
        parent.type = "reduction";
        parent.rule = reduction.rule;
        parent.pivot_id = reduction.pivot_id;
        parent.vec = child_node.vec;
        for (int &d : parent.vec) d += reduction.decrease;
        parent.tau = reduction.decrease == 0
                         ? child_node.tau
                         : branching_factor(parent.vec);
        parent.formula_snapshot = this->get_cert_snapshot();
        parent.rr_witness_clauses = reduction.witness_clauses;
        parent.children.push_back(child_node);
        destroy_cnf(reduction.cnf);
        if (restart.type=="restart" && branching_weight(parent.vec,q)>=1.0L) return restart;
        return parent;
    }

    // Lemmas 2 and 3 apply to arbitrary child formulas, not only to affine
    // residuals produced by group branching.  Keeping this before the depth
    // cutoff is essential: a depth-1 branch must see the lemma in its child.
    DirectLemmaResult direct_lemma;
    if (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
        direct_lemma = find_best_direct_lemma23(*this, q);
    if (direct_lemma.applied && branching_weight(direct_lemma.vec, q) < granted)
    {
        granted = branching_weight(direct_lemma.vec, q);
        granted_node.vec = direct_lemma.vec;
        granted_node.tau = direct_lemma.tau;
        granted_node.rule = direct_lemma.rule;
        granted_node.pivot_id = direct_lemma.pivot_id;
        granted_node.formula_snapshot = this->get_cert_snapshot();
    }

    // Step 4 / Lemma 4.
    // For an (i,j)-literal a, the unit clauses must contain a itself
    // (the side with i occurrences), not its complement.  The resulting
    // branching vector is (i, 2j+1), where i >= j >= 2.
    if (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
    {
        for (auto const &[id, s] : stats)
        {
            auto try_lemma4 = [&](int i, int j, int unit_count)
            {
                if (i >= j && j >= 2 && unit_count >= j - 1)
                {
                    vector<int> step4_branch = {i, 2 * j + 1};
                    long double f = branching_weight(step4_branch, q);
                    if (f < granted)
                    {
                        granted = f;
                        granted_node.vec = step4_branch;
                        granted_node.tau = branching_factor(granted_node.vec);
                        granted_node.rule = "lemma4";
                        granted_node.pivot_id = id;
                        granted_node.formula_snapshot = this->get_cert_snapshot();
                    }
                }
            };

            // a is the positive literal.
            try_lemma4(s.pos_count, s.neg_count, s.pos_unit_count);
            // a is the negative literal.
            try_lemma4(s.neg_count, s.pos_count, s.neg_unit_count);
        }
    }

    // Proof-backed local lemmas are available even with assumptions off.
    // The generator records a leaf; assembly supplies its constructive tree.
    for (const LemmaApplication &application : find_proved_lemma_applications(
             *this, q, int(property1_context) | (2 * int(property2_context))))
    {
        long double weight = branching_weight(application.vector, q);
        if (weight < granted || (weight == granted && granted_node.type == "leaf" && !granted_node.rule.empty()))
        {
            granted = weight;
            granted_node = lemma_application_leaf(*this, application);
        }
    }

    if (depth == 0) return granted_node;

    if (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS && MaxSATSettings.ALLOW_LEMMA3_SPLIT)
    {
        for (const auto &[id, s] : stats)
        {
            if (!((s.pos_count == 2 && s.neg_count == 1) ||
                  (s.pos_count == 1 && s.neg_count == 2))) continue;
            int long_decrease = 0;
            unique_ptr<CNF, decltype(&destroy_cnf)> residual(
                lemma3_resolution(*this, id, long_decrease), destroy_cnf);
            if (!residual) continue;
            ProofNode child;
            {
                ResolutionContext context;
                child = residual->xiao_branch(depth - 1, "", q);
            }
            if (branching_weight(child.vec, q) >= 1.0L)
            {
                child = ProofNode({0});
                child.formula_snapshot = residual->get_cert_snapshot();
            }
            vector<int> branch = {long_decrease};
            for (int d : child.vec) branch.push_back(1 + d);
            // Xiao's statement is a disjunction: a >=1 reduction OR the
            // displayed branching. Its unknown reduction case must remain.
            vector<int> worst = branching_weight(branch, q) >= branching_weight({1}, q)
                                    ? branch : vector<int>{1};
            long double weight = branching_weight(worst, q);
            if (weight < granted)
            {
                granted = weight;
                granted_node = ProofNode(worst);
                granted_node.type = "lemma3_split";
                granted_node.pivot_id = id;
                granted_node.lemma3_long_decrease = long_decrease;
                granted_node.formula_snapshot = get_cert_snapshot();
                granted_node.children.push_back(std::move(child));
            }
        }
    }

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
        ProofNode child1_res = new_cnf1->xiao_branch(depth - 1, "", q);
        ProofNode stop1_res({0});
        stop1_res.formula_snapshot = new_cnf1->get_cert_snapshot();

        // Ветвь 2: x = 0
        auto [reduced_cnt0, new_cnf0] = apply_xiao_assignment(this, var_id, false);
        ProofNode child0_res = new_cnf0->xiao_branch(depth - 1, "", q);
        ProofNode stop0_res({0});
        stop0_res.formula_snapshot = new_cnf0->get_cert_snapshot();

        // Contributions are additive at fixed q: each child independently
        // chooses its continuation or a call (whose weight is one).
        ProofNode selected1 = branching_weight(child1_res.vec, q) < 1.0L
                                  ? child1_res : stop1_res;
        ProofNode selected0 = branching_weight(child0_res.vec, q) < 1.0L
                                  ? child0_res : stop0_res;
        vector<int> current_branching;
        std::vector<bool> imported_sides(2, false);
        std::vector<bool> imported1(2, false);
        auto eligible = property2_context && MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS
                            ? xiao_property2_sides(*this, var_id)
                            : std::array<bool, 2>{false, false};
        auto eligible1 = property1_context && MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS
                            ? xiao_property1_sides(*this, var_id)
                            : std::array<bool, 2>{false, false};
        std::vector<int> property_vector = branching_weight({11, 3}, q) >=
                                         branching_weight({11, 10, 4}, q)
                                             ? std::vector<int>{11, 3}
                                             : std::vector<int>{11, 10, 4};
        auto append_side = [&](int side, ProofNode &selected, const ProofNode &stop, int decrease) {
            std::vector<int> ordinary;
            for (int d : selected.vec) ordinary.push_back(decrease + d);
            if (eligible[side] && branching_weight(property_vector, q) < branching_weight(ordinary, q))
            {
                imported_sides[side] = true;
                selected = stop;
                current_branching.insert(current_branching.end(), property_vector.begin(), property_vector.end());
            }
            else current_branching.insert(current_branching.end(), ordinary.begin(), ordinary.end());
            // Property 1 is a complete bound for this assignment arm, measured
            // before assigning the pivot, just like Property 2.
            std::vector<int> p1 = {18, 11, 11, 4};
            const auto &previous = imported_sides[side] ? property_vector : ordinary;
            if (eligible1[side] && branching_weight(p1, q) < branching_weight(previous, q))
            {
                current_branching.resize(current_branching.size() - previous.size());
                current_branching.insert(current_branching.end(), p1.begin(), p1.end());
                imported_sides[side] = false;
                imported1[side] = true;
                selected = stop;
            }
        };
        append_side(0, selected1, stop1_res, reduced_cnt1);
        append_side(1, selected0, stop0_res, reduced_cnt0);
        long double current_weight = branching_weight(current_branching, q);
        if (!any_var_processed || current_weight < min_weight)
        {
            min_weight = current_weight;
            any_var_processed = true;
            best_node.type = imported_sides[0] || imported_sides[1] ? "xiao_property2_branch" : "branch";
            if (imported1[0] || imported1[1]) best_node.type = "xiao_property1_branch";
            best_node.property2_sides = imported_sides;
            best_node.property1_sides = imported1;
            best_node.property1_scope = lemma_current_degree_scope();
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
