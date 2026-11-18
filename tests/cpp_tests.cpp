#include "cnf.h"
#include "group_cover.h"
#include "strategy_cache.h"
#include "residual_search.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <random>
#include <stdexcept>

using namespace std;

namespace {
void test_safety()
{
    Literal safety_x("safety_x");
    auto rejected = [](auto action) {
        bool caught = false;
        try { action(); } catch (const invalid_argument &) { caught = true; }
        assert(caught);
    };
    unique_ptr<CNF, decltype(&destroy_cnf)> formula(new CNF(), destroy_cnf);
    for (int i = 0; i < MAX_MASK_BITS; ++i)
        formula->clauses.push_back(new Clause(vector<Literal*>{intern_literal(2, false)}));
    assert(!formula->branch({2}).alternatives.empty());
    ProofNode no_cover = formula->branch_group({2}, 0, true);
    assert(no_cover.vec == vector<int>({0}));
    assert(no_cover.formula_snapshot == formula->get_cert_snapshot());
    formula->clauses.push_back(new Clause(vector<Literal*>{intern_literal(2, false)}));
    rejected([&] { formula->branch({2}); });
    rejected([&] { formula->branch_group({2}); });
    assert(!materialize_group_residual(*formula, {2}, {0}).valid);
    delete formula->clauses.back();
    formula->clauses.pop_back();
    rejected([&] { formula->branch({2, 2}); });
    vector<int> ids;
    for (int i = 0; i <= MAX_MASK_BITS; ++i) ids.push_back(i + 2);
    rejected([&] { formula->branch(ids); });
    string diag;
    assert(!check_group_validity({0, 0}, 1, diag));
    assert(!check_group_validity({-1, 0}, 1, diag));
    assert(!check_group_validity({0, 2}, 1, diag));
    assert(!check_group_validity({0}, 31, diag));
    vector<int> oversized_group(32);
    for (int i = 0; i < 32; ++i) oversized_group[i] = i;
    assert(!check_group_validity(oversized_group, 5, diag));
    rejected([] { validate_degree(1, 3, SINGLETON); });
    rejected([] { validate_degree(1, 4, SINGLETON); });
    validate_degree(3, 1, SINGLETON);

    unique_ptr<CNF, decltype(&destroy_cnf)> tied_assignments(
        new CNF(), destroy_cnf);
    for (int i = 0; i < 3; ++i)
    {
        tied_assignments->clauses.push_back(
            new Clause(vector<Literal*>{intern_literal(2, false)}));
        tied_assignments->clauses.push_back(
            new Clause(vector<Literal*>{intern_literal(2, true)}));
    }
    ProofNode tied_branch = tied_assignments->branch({2});
    assert(!tied_branch.alternatives.empty());
    assert(tied_branch.vec == vector<int>({6}));

    unique_ptr<CNF, decltype(&destroy_cnf)> parent(new CNF(), destroy_cnf);
    parent->clauses.push_back(new Clause(vector<Literal*>{intern_literal(2, false),
                                                         &UNKNOWN_NOT_EMPTY_LITERAL}));
    auto children = add_new_var_in_place(parent.get(), "safety_y", [](CNF*) { return 0; },
                                         {{3, 1, SINGLETON}});
    assert(!children.empty());
    for (CNF *child : children)
    {
        assert(analyze_formula(*child).count(VAR2ID.at("safety_y")));
        assert(child->get_cert_snapshot() != parent->get_cert_snapshot());
        destroy_cnf(child);
    }
    cout << "Mask bounds and exposure safety tests passed\n";
}


// Вспомогательная функция для сборки временного CNF из слепка
CNF* create_dummy_cnf(const std::vector<std::vector<int>>& snap) {
    CNF* cnf = new CNF();
    for(const auto& cl : snap) {
        std::vector<Literal*> lits;
        for(int v : cl) {
            if(v == 0) lits.push_back(&UNKNOWN_LITERAL);
            else if(v == 1) lits.push_back(&UNKNOWN_NOT_EMPTY_LITERAL);
            else lits.push_back(new Literal(abs(v), v < 0)); 
        }
        cnf->clauses.push_back(new Clause(lits));
    }
    return cnf;
}

// Очистка фиктивного CNF
void delete_dummy_cnf(CNF* cnf) {
    for(Clause* c : cnf->clauses) {
        for(Literal* l : c->lits) {
            if(l != &UNKNOWN_LITERAL && l != &UNKNOWN_NOT_EMPTY_LITERAL) delete l;
        }
        delete c;
    }
    delete cnf;
}

void test_group_cover()
{
    // Compare direct image generation to the old independent validity test
    // for every subset of the full assignment universe, up to four variables.
    const int expected[] = {1, 3, 11, 49, 257};
    for (int k = 0; k <= 4; ++k)
    {
        set<vector<int>> generated;
        int visits = 0;
        enumerate_substitution_groups(k, [&](const vector<int> &rows) {
            ++visits;
            assert(generated.insert(rows).second);
        });
        assert(visits == expected[k]);
        if (k == 0) continue;
        set<vector<int>> valid;
        for (int subset = 1; subset < (1 << (1 << k)); ++subset)
        {
            vector<int> rows;
            for (int row = 0; row < (1 << k); ++row)
                if (subset & (1 << row)) rows.push_back(row);
            string diag;
            if (check_group_validity(rows, k, diag)) valid.insert(rows);
        }
        assert(generated == valid);
    }

    // Three required rows, two cheap overlapping pairs. Every disjoint
    // partition needs a singleton and costs at least .35 + .5 = .85.
    vector<WeightedGroup> overlapping = {
        {{0, 1}, .35L}, {{0, 2}, .35L},
        {{0}, .5L}, {{1}, .5L}, {{2}, .5L}};
    GroupCover cover = minimum_group_cover(3, overlapping);
    assert(cover.groups == vector<int>({0, 1}));
    assert(fabsl(cover.weight - .7L) < 1e-15L);
    assert(!isfinite(minimum_group_cover(3, overlapping, 1).weight));
    assert(minimum_group_cover(0, {}).weight == 0);
    assert(!isfinite(minimum_group_cover(3, {}).weight));
    assert(!isfinite(minimum_group_cover(3, overlapping, 0).weight));

    // Independent exhaustive oracle for the weighted-cover optimizer,
    // including duplicate coverage, overlap and bounds on the group count.
    mt19937 rng(1741);
    for (int trial = 0; trial < 80; ++trial)
    {
        vector<WeightedGroup> candidates;
        for (int i = 0; i < 8; ++i)
        {
            int image = 1 + rng() % 15;
            vector<int> rows;
            for (int row = 0; row < 4; ++row)
                if (image & (1 << row)) rows.push_back(row);
            candidates.push_back({rows, branching_weight({1 + int(rng() % 12)}, 1.2872)});
        }
        for (int limit : {-1, 1, 2, 3})
        {
            long double optimum = numeric_limits<long double>::infinity();
            for (int subset = 1; subset < (1 << candidates.size()); ++subset)
            {
                int covered = 0, count = 0;
                long double weight = 0;
                for (int i = 0; i < (int)candidates.size(); ++i)
                    if (subset & (1 << i))
                    {
                        ++count;
                        weight += candidates[i].weight;
                        for (int row : candidates[i].coverage) covered |= 1 << row;
                    }
                if (covered == 15 && (limit < 0 || count <= limit))
                    optimum = min(optimum, weight);
            }
            GroupCover actual = minimum_group_cover(4, candidates, limit);
            assert((!isfinite(optimum) && !isfinite(actual.weight)) ||
                   fabsl(actual.weight - optimum) < 1e-12L);
        }
    }
    // Actual CNF: overlap improves even over disjoint covers that are allowed
    // to add dominated rows. All children are constructive, with no imports.
    bool saved_assumptions = MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS;
    int saved_width = MaxSATSettings.MAXIMUM_CLAUSE_SIZE;
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = -1;
    const double q = 1.2872;
    CNF *formula = create_dummy_cnf({
        {2, 0}, {4}, {2, 3, 0}, {4, 0}, {-3},
        {-2, 3, -4, 0}, {-4, 0}, {2}, {-2, -3, 0}, {-3, -4, 0}});
    ProofNode proof = formula->branch_group({2, 3, 4}, -1, true, q);
    assert(proof.vec == vector<int>({6, 8}));
    assert(proof.cover_groups == vector<vector<int>>({{0, 1, 4, 5}, {5, 7}}));
    assert(formula->branch_group({2, 3, 4}, -1, false, q).vec == proof.vec);
    int required = 0;
    for (int row = 0; row < 8; ++row)
        if (!proof.subsumptions.count(row)) required |= 1 << row;
    assert(required == ((1 << 1) | (1 << 4) | (1 << 5) | (1 << 7)));
    vector<pair<int, long double>> costs;
    enumerate_substitution_groups(3, [&](const vector<int> &rows) {
        int coverage = 0;
        for (int row : rows) coverage |= 1 << row;
        coverage &= required;
        if (!coverage) return;
        GroupResidual residual = materialize_group_residual(*formula, {2, 3, 4}, rows);
        assert(residual.valid);
        ProofNode child = analyze_residual(*residual.cnf, q);
        for (int &d : child.vec) d += residual.base_decrease;
        long double cost = branching_weight(child.vec, q);
        if (residual.base_decrease > 0)
            cost = min(cost, branching_weight({residual.base_decrease}, q));
        costs.push_back({coverage, cost});
        destroy_cnf(residual.cnf);
    });
    map<int, long double> disjoint_memo;
    function<long double(int)> disjoint = [&](int remaining) -> long double {
        if (!remaining) return 0;
        if (disjoint_memo.count(remaining)) return disjoint_memo.at(remaining);
        long double best = numeric_limits<long double>::infinity();
        int first = remaining & -remaining;
        for (const auto &[coverage, weight] : costs)
            if ((coverage & first) && (coverage & remaining) == coverage)
                best = min(best, weight + disjoint(remaining ^ coverage));
        return disjoint_memo[remaining] = best;
    };
    assert(fabsl(disjoint(required) - branching_weight({6, 7}, q)) < 1e-12L);
    assert(branching_weight(proof.vec, q) < disjoint(required));

    // Independently check the semantic identity at every tail valuation,
    // including the overlapping row and all additional dominated rows.
    map<int, int> tail_index;
    for (const auto &clause : proof.formula_snapshot)
        for (int literal : clause)
            if (literal >= SNAP_TAIL_ANY_BASE && !tail_index.count(literal))
                tail_index.emplace(literal, tail_index.size());
    auto optimum = [&](const vector<vector<int>> &snapshot, int boundary) {
        int best = 0;
        for (int assignment = 0; assignment < 8; ++assignment)
        {
            int score = 0;
            for (const auto &clause : snapshot)
            {
                bool satisfied = false;
                for (int literal : clause)
                {
                    if (literal >= SNAP_TAIL_ANY_BASE)
                        satisfied |= (boundary >> tail_index.at(literal)) & 1;
                    else
                        satisfied |= bool((assignment >> (abs(literal) - 2)) & 1) == (literal > 0);
                }
                score += satisfied;
            }
            best = max(best, score);
        }
        return best;
    };
    for (int boundary = 0; boundary < (1 << tail_index.size()); ++boundary)
    {
        int children_best = 0;
        for (size_t i = 0; i < proof.alternatives.size(); ++i)
        {
            const auto &alternative = proof.alternatives[i];
            assert(alternative.represented_masks == proof.cover_groups[i]);
            assert(alternative.decrease == int(proof.formula_snapshot.size()) -
                   int(alternative.proof->formula_snapshot.size()));
            children_best = max(children_best, alternative.offset +
                optimum(alternative.proof->formula_snapshot, boundary));
        }
        assert(optimum(proof.formula_snapshot, boundary) == children_best);
    }
    delete_dummy_cnf(formula);
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = saved_assumptions;
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = saved_width;
    // Four selected variables, all 16 assignments undominated. This used to
    // require enumerating partitions of a 16-element set.
    vector<vector<int>> four_snapshot;
    for (int var = 2; var <= 5; ++var)
        for (int copy = 0; copy < 2; ++copy)
        {
            four_snapshot.push_back({var, 0});
            four_snapshot.push_back({-var, 0});
        }
    CNF *four = create_dummy_cnf(four_snapshot);
    ProofNode four_proof = four->branch_group({2, 3, 4, 5}, -1, true, q);
    assert(four_proof.subsumptions.empty());
    assert(four->branch_group({2, 3, 4, 5}, -1, false, q).vec == four_proof.vec);
    delete_dummy_cnf(four);
    cout << "Substitution groups and exact weighted cover tests passed\n";
}

void test_strategy_cache()
{
    const double q = 1.2872;
    bool saved_assumptions = MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS;
    int saved_width = MaxSATSettings.MAXIMUM_CLAUSE_SIZE;
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = -1;
    set_strategy_cache_enabled(true);
    CNF *first = create_dummy_cnf({{2, 0}, {-2, 0}});
    CNF *renamed = create_dummy_cnf({{2, 0}, {-2, 0}});
    ProofNode original = analyze_residual(*first, q);
    assert(strategy_cache_stats().misses == 1);
    ProofNode hit = analyze_residual(*renamed, q);
    assert(strategy_cache_stats().hits == 1);
    assert(hit.formula_snapshot == renamed->get_cert_snapshot());
    assert(hit.formula_snapshot != original.formula_snapshot);
    assert(hit.vec == original.vec);
    assert(hit.children.size() == 1 && hit.children[0].formula_snapshot.size() == 1);
    std::set<int> current_tails;
    for (const auto &clause : renamed->get_cert_snapshot())
        for (int literal : clause)
            if (literal >= SNAP_TAIL_ANY_BASE) current_tails.insert(literal);
    for (int literal : hit.children[0].formula_snapshot[0])
        assert(current_tails.count(literal));
    hit.children[0].formula_snapshot.clear();
    assert(!analyze_residual(*renamed, q).children[0].formula_snapshot.empty());

    auto misses = strategy_cache_stats().misses;
    analyze_residual(*renamed, 1.5);
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    analyze_residual(*renamed, q);
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = 3;
    analyze_residual(*renamed, q);
    assert(strategy_cache_stats().misses == misses + 3);
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = -1;

    // Tail type, sharing, and clause order are part of the key.
    CNF *typed = new CNF(*first);
    typed->clauses[0]->lits.erase(&UNKNOWN_LITERAL);
    typed->clauses[0]->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);
    typed->clauses[0]->tail_atoms.begin()->second = true;
    CNF *shared = new CNF(*first);
    shared->clauses[1]->tail_atoms = shared->clauses[0]->tail_atoms;
    CNF *reordered = new CNF(*first);
    reverse(reordered->clauses.begin(), reordered->clauses.end());
    misses = strategy_cache_stats().misses;
    analyze_residual(*typed, q);
    analyze_residual(*shared, q);
    analyze_residual(*reordered, q);
    assert(strategy_cache_stats().misses == misses + 3);
    destroy_cnf(typed);
    destroy_cnf(shared);
    destroy_cnf(reordered);
    delete_dummy_cnf(first);
    delete_dummy_cnf(renamed);

    // Check that the full RR chain is identical with and without caching.
    CNF *cascade = create_dummy_cnf({{2, 3}, {-2, 3}, {-3, 0}});
    set_strategy_cache_enabled(false);
    ProofNode uncached = analyze_residual(*cascade, q);
    set_strategy_cache_enabled(true);
    ProofNode cached = analyze_residual(*cascade, q);
    ProofNode repeated = analyze_residual(*cascade, q);
    assert(strategy_cache_stats().hits == 1);
    assert(cached.vec == uncached.vec && repeated.vec == uncached.vec);
    assert(cached.formula_snapshot == cascade->get_cert_snapshot());
    assert(cached.rule == "RR2" && cached.children[0].rule == "RR2");
    assert(cached.children[0].children[0].formula_snapshot ==
           uncached.children[0].children[0].formula_snapshot);
    delete_dummy_cnf(cascade);

    CNF *group_input = create_dummy_cnf({
        {0, 2, 3}, {0, 2, 4}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3}, {0, 3}, {-3}, {0, -4}, {0, -4}});
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    set_strategy_cache_enabled(false);
    ProofNode without_cache = group_input->branch_group({2, 3, 4}, -1, true, q);
    set_strategy_cache_enabled(true);
    ProofNode with_cache = group_input->branch_group({2, 3, 4}, -1, true, q);
    function<bool(const ProofNode &, const ProofNode &)> same_proof;
    same_proof = [&](const ProofNode &a, const ProofNode &b) {
        if (a.type != b.type || a.rule != b.rule || a.pivot_id != b.pivot_id ||
            a.vec != b.vec || a.formula_snapshot != b.formula_snapshot ||
            a.cover_groups != b.cover_groups ||
            a.reduced_cnt_true != b.reduced_cnt_true || a.reduced_cnt_false != b.reduced_cnt_false ||
            a.offset_true != b.offset_true || a.offset_false != b.offset_false ||
            a.children.size() != b.children.size() || a.alternatives.size() != b.alternatives.size())
            return false;
        for (size_t i = 0; i < a.children.size(); ++i)
            if (!same_proof(a.children[i], b.children[i])) return false;
        for (size_t i = 0; i < a.alternatives.size(); ++i)
        {
            const auto &left = a.alternatives[i], &right = b.alternatives[i];
            if (left.offset != right.offset || left.decrease != right.decrease ||
                left.represented_masks != right.represented_masks ||
                bool(left.proof) != bool(right.proof)) return false;
            if (left.proof && !same_proof(*left.proof, *right.proof)) return false;
        }
        return true;
    };
    assert(same_proof(without_cache, with_cache));
    assert(same_proof(with_cache, group_input->branch_group({2, 3, 4}, -1, true, q)));
    assert(strategy_cache_stats().hits > 0);
    delete_dummy_cnf(group_input);

    clear_strategy_cache();
    for (int i = 0; i < 2100; ++i)
    {
        CNF formula;
        formula.clauses.push_back(new Clause(vector<Literal *>{intern_literal(100 + i, false)}));
        cached_strategy_search(formula, q, [&] {
            ProofNode call({0});
            call.formula_snapshot = formula.get_cert_snapshot();
            return call;
        });
        delete formula.clauses[0];
    }
    assert(strategy_cache_stats().entries <= 2048);
    assert(strategy_cache_stats().evictions > 0);
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = saved_assumptions;
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = saved_width;
    clear_strategy_cache();
    cout << "Residual strategy cache tests passed\n";
}

void test_step51()
{
    bool saved = MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS;
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    for (int sign : {1, -1})
    {
        CNF *formula = create_dummy_cnf({
            {2 * sign, 0, 1}, {2 * sign, 0}, {2 * sign, 0},
            {-2 * sign}, {-2 * sign, 0}});
        ProofNode proof = analyze_residual(*formula, 1.2872);
        assert(proof.type == "branch" && proof.rule.empty());
        assert(proof.pivot_id == 2 && proof.children.size() == 2);
        assert(proof.vec == (sign == 1 ? vector<int>{4, 2} : vector<int>{2, 4}));
        assert(proof.offset_true == (sign == 1 ? 3 : 2));
        assert(proof.offset_false == (sign == 1 ? 2 : 3));
        for (const auto &child : proof.children)
        {
            assert(child.type == "leaf" && child.rule.empty() && child.vec == vector<int>{0});
            // Mixed boundary markers survive in the full instance but the
            // tail-only clause leaves this local assignment snapshot.
            assert(child.formula_snapshot.empty());
        }
        delete_dummy_cnf(formula);
    }
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = saved;
    cout << "Constructive Step 5.1 tests passed\n";
}

void test_weighted_search()
{
    const double q = 1.2872;
    assert(branching_factor({1, 8}) < branching_factor({2, 5}));
    assert(branching_weight({2, 5}, q) < branching_weight({1, 8}, q));
    assert(branching_weight({0}, q) == 1.0L);
    assert(!meets_branching_target({0}, q));
    assert(!meets_branching_target({0, 8}, q));
    assert(!meets_branching_target({}, q));
    assert(meets_branching_target({1, 1}, 2.0));
    assert(!meets_branching_target({1, 1}, 1.9));
    bool rejected = false;
    try { branching_weight({1}, 1.0); }
    catch (const invalid_argument &) { rejected = true; }
    assert(rejected);

    // Both lemmas apply without an intervening RR.  Their cost curves cross:
    // the chosen root strategy must change when the target changes.
    CNF *input = create_dummy_cnf({
        {2, 0}, {2, 0}, {-2, 0},
        {3}, {3, 0}, {-3, 0}, {-3, 0}});
    bool saved_assumptions = MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS;
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    ProofNode low = analyze_residual(*input, 1.233);
    ProofNode high = analyze_residual(*input, q);
    assert(low.rule == "lemma3" && low.vec == vector<int>({1, 8}));
    assert(high.rule == "lemma4" && high.vec == vector<int>({2, 5}));
    // Repeated changes of q must not reuse a previous target's choice.
    assert(analyze_residual(*input, 1.233).vec == low.vec);
    for (double target : {1.233, q, 1.5})
    {
        ProofNode group = input->branch_group({2, 3}, -1, false, target);
        ProofNode proof = input->branch_group({2, 3}, -1, true, target);
        assert(group.vec == proof.vec);
    }
    ProofNode lemma4_reduction_bound = analyze_residual(*input, 1.5);
    assert(lemma4_reduction_bound.rule == "lemma4");
    assert(lemma4_reduction_bound.vec == vector<int>({1}));
    assert(lemma4_reduction_bound.assumption_branch_vector == vector<int>({2, 5}));

    CNF *two_singletons = create_dummy_cnf({
        {2, 0}, {2, 0}, {-2}, {-3, 0}, {-3, 0}, {3}});
    ProofNode composed = analyze_residual(*two_singletons, q);
    assert(composed.rule == "double_lemma3" && composed.vec == vector<int>({2, 9, 8}));
    ProofNode double_reduction_bound = analyze_residual(*two_singletons, 1.5);
    assert(double_reduction_bound.rule == "double_lemma3");
    assert(double_reduction_bound.vec == vector<int>({1}));
    assert(double_reduction_bound.assumption_branch_vector == composed.vec);
    delete_dummy_cnf(two_singletons);

    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = saved_assumptions;
    delete_dummy_cnf(input);
    cout << "Fixed-target weighted search tests passed\n";
}

static vector<vector<int>> sorted_snapshot(CNF *cnf)
{
    vector<vector<int>> snapshot = cnf->get_snapshot();
    for (auto &clause : snapshot)
        sort(clause.begin(), clause.end());
    sort(snapshot.begin(), snapshot.end());
    return snapshot;
}

static void check_constructive_reduction(const vector<vector<int>> &input,
                                         const string &expected_rule,
                                         int expected_decrease,
                                         vector<vector<int>> expected_formula,
                                         bool isolate_rule = false)
{
    CNF *cnf = create_dummy_cnf(input);
    ReductionStep step = isolate_rule
                             ? apply_named_reduction(*cnf, expected_rule)
                             : apply_first_reduction(*cnf);
    assert(step.applied);
    assert(step.rule == expected_rule);
    assert(step.decrease == expected_decrease);
    for (auto &clause : expected_formula)
        sort(clause.begin(), clause.end());
    sort(expected_formula.begin(), expected_formula.end());
    assert(sorted_snapshot(step.cnf) == expected_formula);
    destroy_cnf(step.cnf);
    delete_dummy_cnf(cnf);
}

void test_constructive_reductions()
{
    check_constructive_reduction({{2, -2, 3}, {4, 0}},
                                 "RR1", 1, {{4, 0}}, true);
    check_constructive_reduction({{2, 0}, {-2, 1}},
                                 "RR2", 1, {{0, 1}});
    check_constructive_reduction({{2}, {2, 0}, {-2, 1}},
                                 "RR3", 2, {{1}});
    check_constructive_reduction({{2, 3}, {-2, 3}, {2, 0}, {-2, 1},
                                  {-3, 0}, {-3, 1}},
                                 "RR4", 1,
                                 {{3}, {2, 0}, {-2, 1}, {-3, 0}, {-3, 1}});
    check_constructive_reduction({{2, 3}, {2, 4}, {-2, 5}},
                                 "RR5", 1,
                                 {{3, 5}, {-3, 4, 5}}, true);
    check_constructive_reduction({{2, 0}, {2, 1}, {-2, 3, 0},
                                  {3, 1}, {-3, 0}},
                                 "RR6", 1,
                                 {{3, 0}, {3, 0, 1}, {3, 1}, {-3, 0}});
    check_constructive_reduction({{2, 3}, {2, 3, 4},
                                  {-2, -3, 5}, {-3, 6}},
                                 "RR7", 0,
                                 {{2, -2}, {2, -2, 4},
                                  {-2, 2, 5}, {2, 6}}, true);
    check_constructive_reduction({{2, 3, 4}, {-2, -3, 5}, {-2, 6}},
                                 "RR8", 1,
                                 {{-2, -3, 5}, {-2, 6}}, true);
    check_constructive_reduction({{2, 4}, {2, 5},
                                  {-2, 3, 6}, {-2, 3, 7}, {-3}},
                                 "RR9", 0,
                                 {{3, 4, 6}, {3, 4, 7},
                                  {3, 5, 6}, {3, 5, 7}, {-3}}, true);

    CNF *cascade_input = create_dummy_cnf({{2, 3}, {-2, 3}, {-3, 0}});
    ReductionFixpoint cascade = reduce_to_fixpoint(*cascade_input);
    assert(cascade.total_decrease == 2);
    assert(cascade.steps.size() == 2);
    assert(cascade.steps[0].rule == "RR2");
    assert(cascade.steps[1].rule == "RR2");
    vector<vector<int>> cascade_expected = {{0}};
    assert(sorted_snapshot(cascade.cnf) == cascade_expected);
    destroy_cnf(cascade.cnf);
    delete_dummy_cnf(cascade_input);

    CNF *lemma3_input = create_dummy_cnf({{0, 4}, {0, -4}, {0, -4}});
    ProofNode lemma3 = analyze_residual(*lemma3_input, 1.2873);
    assert(lemma3.rule == "lemma3");
    assert(lemma3.vec == vector<int>({1, 8}));

    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    ProofNode strict_lemma3 = analyze_residual(*lemma3_input, 1.2873);
    assert(strict_lemma3.rule.empty());
    assert(strict_lemma3.vec == vector<int>({0}));
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    delete_dummy_cnf(lemma3_input);

    CNF *missing_position = create_dummy_cnf({{2}, {-2}});
    vector<CNF *> unchanged = add_new_var_in_place(
        missing_position, "missing_position_witness",
        [](CNF *) { return -1; });
    assert(unchanged.size() == 1);
    assert(unchanged[0] == missing_position);
    delete_dummy_cnf(missing_position);

    // Regression from the remaining (3,2)-case: after either assignment of
    // x, z becomes a 3-variable and Lemma 3 must be composed in the child.
    CNF *child_pipeline = create_dummy_cnf({
        {0, 2, 3}, {0, 2, 4}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3}, {0, 3}, {-3}, {0, -4}, {0, -4}});
    const vector<int> expected_child_vec = {11, 10, 4, 3};
    ProofNode grouped_child = child_pipeline->branch_group({2, 3, 4});
    assert(is_permutation(grouped_child.vec.begin(), grouped_child.vec.end(),
                          expected_child_vec.begin(), expected_child_vec.end()));
    assert(grouped_child.tau < 1.28855);
    delete_dummy_cnf(child_pipeline);

    // Step 5.3: z is a (4,1)-singleton.  Continue with RR6 in z=1,
    // but leave z=0 as a recursive stop instead of forcing Lemma 2 there.
    CNF *step53_input = create_dummy_cnf({
        {0, 2, 3}, {0, 2}, {0, 2}, {1, -2, 3}, {0, -2, 4},
        {0, 3, 4}, {0, 3, 4}, {-3}, {0, 4}, {-4}});
    vector<int> expected_step53 = {6, 1};
    ProofNode step53_group = step53_input->branch_group({2, 3, 4});
    assert(branching_weight(step53_group.vec, 1.2873) <= branching_weight(expected_step53, 1.2873));
    delete_dummy_cnf(step53_input);

    auto check_step55 = [&](const vector<vector<int>> &formula)
    {
        CNF *input = create_dummy_cnf(formula);
        vector<int> expected = {11, 10, 4, 3};
        ProofNode grouped = input->branch_group({2, 3, 4});
        assert(branching_weight(grouped.vec, 1.2873) <= branching_weight(expected, 1.2873));
        delete_dummy_cnf(input);
    };

    check_step55({
        {1, 2}, {0, 2}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3, 4}, {0, 3}, {-3}, {0, 4}, {-4}});
    check_step55({
        {1, 2}, {0, 2}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3}, {0, 3}, {-3}, {0, 4}, {0, 4}, {-4}});

    cout << "RR1--RR9 constructive tests passed\n";
}

} // namespace

int main()
{
    preprocess();
    test_weighted_search();
    test_strategy_cache();
    test_group_cover();
    test_constructive_reductions();
    test_safety();
    test_step51();
}
