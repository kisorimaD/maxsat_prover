#include "cnf.h"
#include "test.h"
#include "cert_logger.h"
#include "strategy_cache.h"
#include "group_cover.h"

#include <algorithm>
#include <assert.h>
#include <iostream>
#include <sstream>
#include <iomanip>
#include <functional>
#include <stdexcept>
#include <cmath>
#include <random>

using namespace std;

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
        ProofNode child = analyze_residual(*residual.cnf, 1, q);
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
    ProofNode original = first->xiao_branch(1, "", q);
    assert(strategy_cache_stats().misses == 1);
    ProofNode hit = renamed->xiao_branch(1, "", q);
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
    assert(!renamed->xiao_branch(1, "", q).children[0].formula_snapshot.empty());

    auto misses = strategy_cache_stats().misses;
    renamed->xiao_branch(1, "", 1.5);
    renamed->xiao_branch(2, "", q);
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    renamed->xiao_branch(1, "", q);
    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = 3;
    renamed->xiao_branch(1, "", q);
    assert(strategy_cache_stats().misses == misses + 4);
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
    typed->xiao_branch(1, "", q);
    shared->xiao_branch(1, "", q);
    reordered->xiao_branch(1, "", q);
    assert(strategy_cache_stats().misses == misses + 3);
    destroy_cnf(typed);
    destroy_cnf(shared);
    destroy_cnf(reordered);
    delete_dummy_cnf(first);
    delete_dummy_cnf(renamed);

    // Group residual processing has its own search policy. Check a full RR
    // chain and that its cached proof is identical to uncached processing.
    CNF *cascade = create_dummy_cnf({{2, 3}, {-2, 3}, {-3, 0}});
    set_strategy_cache_enabled(false);
    ProofNode uncached = analyze_residual(*cascade, 1, q);
    set_strategy_cache_enabled(true);
    ProofNode cached = analyze_residual(*cascade, 1, q);
    ProofNode repeated = analyze_residual(*cascade, 1, q);
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
        cached_strategy_search(formula, StrategySearchKind::Variable, 0, q, [&] {
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
    ProofNode low = input->xiao_branch(0, "", 1.233);
    ProofNode high = input->xiao_branch(0, "", q);
    assert(low.rule == "lemma3" && low.vec == vector<int>({1, 8}));
    assert(high.rule == "lemma4" && high.vec == vector<int>({2, 5}));
    // Repeated changes of q must not reuse a previous target's choice.
    assert(input->xiao_branch(0, "", 1.233).vec == low.vec);
    for (double target : {1.233, q, 1.5})
    {
        ProofNode variable = input->xiao_branch(1, "", target);
        ProofNode group = input->branch_group({2, 3}, -1, false, target);
        ProofNode proof = input->branch_group({2, 3}, -1, true, target);
        assert(branching_weight(group.vec, target) <= branching_weight(variable.vec, target));
        assert(group.vec == proof.vec);
    }
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = saved_assumptions;
    delete_dummy_cnf(input);
    cout << "Fixed-target weighted search tests passed\n";
}

void test_basics()
{
    Literal a("a");
    Literal b("b");

    Literal na = a.neg();
    vector<Literal *> vec_lits = {&a, &b, &na, &UNKNOWN_LITERAL};
    Clause c(vec_lits);
    Clause d = c;

    Literal nb = b.neg();

    d.lits.insert(&nb);

    print_clause(c);
    print_clause(d);

    Clause unk;

    print_clause(unk);
}

void test_simple_branch()
{}

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
    DirectLemmaResult lemma3 = find_best_direct_lemma23(*lemma3_input);
    assert(lemma3.applied);
    assert(lemma3.rule == "lemma3");
    assert(lemma3.vec == vector<int>({1, 8}));

    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = false;
    ProofNode strict_lemma3 = lemma3_input->xiao_branch(0);
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
    ProofNode child_result = child_pipeline->xiao_branch(1);
    vector<int> expected_child_vec = {11, 10, 4, 3};
    sort(expected_child_vec.begin(), expected_child_vec.end(), greater<int>());
    assert(child_result.vec == expected_child_vec);
    assert(child_result.tau < 1.28855);
    ProofNode grouped_child = child_pipeline->branch_group({2, 3, 4});
    assert(grouped_child.vec == expected_child_vec);
    assert(grouped_child.tau < 1.28855);
    delete_dummy_cnf(child_pipeline);

    // Step 5.3: z is a (4,1)-singleton.  Continue with RR6 in z=1,
    // but leave z=0 as a recursive stop instead of forcing Lemma 2 there.
    CNF *step53_input = create_dummy_cnf({
        {0, 2, 3}, {0, 2}, {0, 2}, {1, -2, 3}, {0, -2, 4},
        {0, 3, 4}, {0, 3, 4}, {-3}, {0, 4}, {-4}});
    vector<int> expected_step53 = {6, 1};
    ProofNode step53_xiao = step53_input->xiao_branch(1);
    assert(step53_xiao.vec == expected_step53);
    assert(step53_xiao.tau < 1.28855);
    ProofNode step53_group = step53_input->branch_group({2, 3, 4});
    assert(branching_weight(step53_group.vec, 1.2873) <= branching_weight(step53_xiao.vec, 1.2873));
    delete_dummy_cnf(step53_input);

    auto check_step55 = [&](const vector<vector<int>> &formula)
    {
        CNF *input = create_dummy_cnf(formula);
        vector<int> expected = {11, 10, 4, 3};
        ProofNode xiao = input->xiao_branch(1);
        assert(xiao.vec == expected);
        assert(xiao.tau < 1.28855);
        ProofNode grouped = input->branch_group({2, 3, 4});
        assert(branching_weight(grouped.vec, 1.2873) <= branching_weight(xiao.vec, 1.2873));
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

void test_branching_factor()
{
    cout << branching_factor({6, 6, 5, 5}) << endl;
    cout << branching_factor({1, 2}) << endl;
    cout << branching_factor({4}) << endl;
}

void test_branch_three_vars()
{}

void test_branch_two_vars()
{}

void test_subset_func()
{
    while (true)
    {
        int A, B;
        if (!(cin >> A)) break;

        if (A == -1)
            break;

        if (!(cin >> B)) break;

        cout << (is_A_subset_of_B(A, B) ? "YES\n" : "NO\n");
    }
}

void test_add_new_var()
{
    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    print_cnf(*with_x);

    cout << "Добавляем переменную y (3, 2)-литерал\n";

    vector<CNF *> with_y = add_new_var(with_x, "y", 3, 2, ANY);

    cout << "Размер " << with_y.size() << endl;
    for (int i = 0; i < 10; ++i)
    {
        print_cnf(*with_y[i]);
    }
}


void pretty_branch_print(vector<string> &vars, CNF *cnf)
{
    int k = vars.size();

    map<int, int> id2ind;

    for (int i = 0; i < k; ++i)
    {
        id2ind[VAR2ID[vars[i]]] = i;
    }

    print_cnf(*cnf);

    for (int i = 0; i < k; ++i)
    {
        cout << vars[i] << '\t';
    }

    for (int i = 0; i < (int)cnf->clauses.size(); ++i)
    {
        cout << i + 1;
        cout << '\t';
    }

    cout << endl;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        for (int i = 0; i < k; ++i)
        {
            cout << ((mask >> i) & 1) << '\t';
        }

        for (int i = 0; i < (int)cnf->clauses.size(); ++i)
        {
            bool find_another_literal = false;
            bool find_true = false;

            for (Literal *l : cnf->clauses[i]->lits)
            {
                if (id2ind.count(l->id) != 0)
                {
                    if (((mask >> id2ind[l->id]) & 1) ^ l->inv)
                    {
                        find_true = true;
                    }
                }
                else
                {
                    find_another_literal = true;
                }
            }

            string res = "?";
            if (find_true)
            {
                res = "YES";
            }
            else if (!find_another_literal)
            {
                res = "NO";
            }
            cout << res << '\t';
        }

        cout << endl;
    }
}

void test_no_unknown_literal()
{

    // CNF cnf;

    // CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);

    // cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    // print_cnf(*with_x);

    // cout << "Добавляем переменную y (3, 2)-литерал\n";

    // vector<CNF *> with_y = add_new_var(with_x, "y", 4, 1, SINGLETON);

    // cout << "Размер: " << with_y.size() << endl;

    // cout << "Введите номер клозы для проверки разбора. -1 для окончания теста\n";

    // int k;
    // cin >> k;

    // vector<string> vars = {"x", "y"};

    // Literal x = Literal("x");
    // Literal y = Literal("y");

    // while (k != -1)
    // {
    //     pretty_branch_print(vars, with_y.at(k));

    //     vector<int> reg_branch = with_y.at(k)->branch({x.id, y.id});
    //     vector<int> group_branch = with_y.at(k)->branch_group({x.id, y.id});

    //     cout << "Regular Branch:\n";
    //     for (int r : reg_branch)
    //         cout << r << " ";
    //     cout << endl;

    //     cout << "Group Branch:\n";
    //     for (int r : group_branch)
    //         cout << r << " ";
    //     cout << endl;

    //     cin >> k;
    // }
}

function<int(CNF *)> create_pos_func(set<Literal *, LiteralPtrLess> need_lits, set<Literal *, LiteralPtrLess> no_lits)
{
    return [need_lits, no_lits](CNF *cnf)
    {
        for (int i = 0; i < cnf->clauses.size(); ++i)
        {
            Clause *now_clause = cnf->clauses[i];

            if (!now_clause->lits.count(&UNKNOWN_LITERAL) &&
                !now_clause->lits.count(&UNKNOWN_NOT_EMPTY_LITERAL))
            {
                continue;
            }

            bool flag = false;

            // print_clause(*now_clause);

            for (Literal *l : now_clause->lits)
            {

                // cout << "compare(" << (*need_lits.begin())->id << "," << l->id << ") = "
                //      << LiteralPtrLess{}((*need_lits.begin()), l) << " / "
                //      << LiteralPtrLess{}(l, (*need_lits.begin())) << endl;

                if (no_lits.find(l) != no_lits.end())
                {
                    // cout << "break!" << endl;
                    flag = true;
                    break;
                }
            }
            // cout << endl;

            for (Literal *l : need_lits)
            {
                if (now_clause->lits.find(l) == now_clause->lits.end())
                {
                    flag = true;
                    break;
                }
            }

            if (!flag)
                return i;
        }

        return -1;
    };
}

int progress_counter_test = 0;

void printProgress_test(double percentage)
{
    int pb_length = 60;
    int val = static_cast<int>(percentage * 100);
    int lpad = static_cast<int>(percentage * pb_length);
    int rpad = pb_length - lpad;
    std::cout << "\r" << val << "% [" << std::string(lpad, '#') << std::string(rpad, '-') << "]" << std::flush;
}

void branch_epoch_universal(vector<CNF *> &variants, vector<int> &ids, double C, bool is_group_branch, bool is_xiao_branch, int xiao_depth = 1)
{
    cout << "Начинается примитивная фильтрация\n";
    vector<CNF *> filtered_variants;

    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        ProofNode naive_node = cnf->branch(ids); // Используем ProofNode

        if (!meets_branching_target(naive_node.vec, C))
        {  
            filtered_variants.push_back(cnf);
        }
        else
        {
            global_logger.log_proof_tree(cnf->node_id, naive_node);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    if(is_xiao_branch)
    {
        cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с Reduction Rules\n";

        swap(filtered_variants, variants);
        filtered_variants.clear();

        for (int i = 0; i < variants.size(); ++i)
        {
            CNF *cnf = variants[i];
            ProofNode rr_node = cnf->xiao_branch(xiao_depth, "", C);

            if (!meets_branching_target(rr_node.vec, C)) {
                filtered_variants.push_back(cnf);
            }
            else
            {
                global_logger.log_proof_tree(cnf->node_id, rr_node);
            }
        }
        
        cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";
        
        cout << "Осталось [" << filtered_variants.size() << "]\n\n";

    }


    if (!is_group_branch)
    {
        swap(filtered_variants, variants);
        return;
    }

    cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с группировкой\n";

    bool need_pb = false;
    if (!filtered_variants.empty() &&
        (ids.size() >= 5 || filtered_variants.size() > (1000u >> (2 * ids.size()))))
    {
        need_pb = true;
        cout << "\nWARNING! Слишком большой размер оставшегося массива, бренчинг с группировкой может работать очень медленно.\n\n";
    }

    swap(variants, filtered_variants);
    filtered_variants.clear();

    if (need_pb)
        progress_counter_test = 0;

    int vsize = variants.size();


    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        // Analyze the groups once and solve one unrestricted weighted cover.
        // Constructive residual proofs are already retained by group analysis.
        ProofNode group_node = cnf->branch_group(ids, -1, true, C);
        if (!meets_branching_target(group_node.vec, C))
            filtered_variants.push_back(cnf);
        else
            global_logger.log_proof_tree(cnf->node_id, group_node);

        if (need_pb)
            progress_counter_test++;

        if (need_pb && progress_counter_test % 5 == 0)
        {
            printProgress_test((double)progress_counter_test / vsize);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    cout << "Осталось [" << filtered_variants.size() << "]\n\n";

    swap(variants, filtered_variants);

    return;
}

void print_help_universal()
{
    cout << "Список команд:\n";
    cout << "   add [var_name] [i] [j] [SINGLETON | ANY]\t\tЗадать корневое семейство один раз; SINGLETON требует j = 1\n";
    cout << "   addlit [i] [j] [SINGLETON | ANY]       \t\tДобавить тип в список возможных литералов на время запуска\n";
    cout << "   addpos [var_name] [need_names] [no_names]\t\tДобавить новую переменную в первую клозу, в которой есть все\n\t\t\t\t\t\t\tпеременные из need_names и нет ни одной из no_names. Ввод разделяется строчками\n";
    cout << "   sv [mask]                               \t\tУстановить возможные типы литералов по показанной битовой маске\n";
    cout << "   set [branching factor]                  \t\tУстановить порог C (по умолчанию 1.2873)\n";
    cout << "   assumptions [on | off]                 \t\tРазрешить/запретить все named-assumption leaves\n";
    cout << "   branch                                  \t\tОбычное отсеивание + с группировкой бренчингом всех вариантов ниже С\n";
    cout << "   simple_branch                           \t\tОбычное отсеивание без группировки бренчингом всех вариантов ниже С\n";
    cout << "   target [i]                              \t\tОставить в рассмотрении только [i] вариант\n";
    cout << "   head [n]                                \t\tВывести [n] первых вариантов сейчас\n";
    cout << "   print [i]                               \t\tВывести [i] вариант и разобрать по переменным\n";
    cout << "   stats                                   \t\tВывести минимум и максимум branching factor среди оставшихся вариантов\n";
    cout << "   cache_stats                             \t\tСтатистика кеша остаточных формул\n";
    cout << "   factor [vector]                         \t\tВывести branching factor для заданного вектора\n";
    cout << "   setposfunc [need_names] [no_names]      \t\tЗафиксировать позиционную функцию, которая будет выводиться в print\n";
    cout << "   empty_divide [i]                        \t\tПрименить empty_divide к [i] формуле (или ко всем, если i = -1)\n";
    cout << "   help                                    \t\tВывести список команд (этот)\n";
    cout << "   exit                                    \t\tВыйти из тестирования\n\n";
}
namespace {
template<class... Values>
void read_arguments(Values&... values)
{
    if (!(cin >> ... >> values))
        throw runtime_error("Incomplete or invalid command arguments");
}

void read_command_line(string &line)
{
    if (!getline(cin, line))
        throw runtime_error("Incomplete multiline command");
}

// Frontiers borrow pointers; this owner releases formulas once they leave cur.
class FrontierOwner {
    using Owner = unique_ptr<CNF, decltype(&destroy_cnf)>;
    map<CNF*, Owner> owned;
public:
    void adopt(const vector<CNF*> &formulas) {
        for (CNF *formula : formulas)
            if (!owned.count(formula))
                owned.emplace(formula, Owner(formula, destroy_cnf));
    }
    void retain(const vector<CNF*> &formulas) {
        adopt(formulas);
        set<CNF*> live(formulas.begin(), formulas.end());
        for (auto it = owned.begin(); it != owned.end(); )
            if (!live.count(it->first)) it = owned.erase(it);
            else ++it;
    }
};
}

void test_universal()
{
    progress_counter_test = 0;

    auto posfunc = create_pos_func(set<Literal *, LiteralPtrLess>(), set<Literal *, LiteralPtrLess>());

    vector<LiteralDegType> variants;
    for (const LiteralDegType &literal : POSSIBLE_LITERALS)
    {
        // (2,1)-типы доступны через sv, но по умолчанию выключены.
        if (literal.i != 2 || literal.j != 1)
            variants.push_back(literal);
    }

    FrontierOwner owner;
    vector<CNF *> cur = {new CNF()};
    owner.adopt(cur);
    bool root_initialized = false;

    vector<int> ids;
    vector<string> vars;

    string command;

    print_help_universal();

    // double C = 1.28855;
    double C = 1.2873;

    while (command != "exit")
    {
        cout << "Введите команду: ";
        owner.retain(cur);
        if (!(cin >> command)) break;

        if (command == "add")
        {
            string var_name;
            int i, j;
            string type;

            read_arguments(var_name, i, j, type);

            if (root_initialized)
                throw invalid_argument("add can only initialize the root; use addpos");
            if (type != "SINGLETON" && type != "ANY" && type != "a")
                throw invalid_argument("expected SINGLETON or ANY");
            LitType new_type = type == "SINGLETON" ? SINGLETON : ANY;
            validate_degree(i, j, new_type);

            if (VAR2ID.count(var_name) != 0)
            {
                cout << "Это имя переменной уже занято. Попробуйте другое название переменной\n";
                continue;
            }

            Literal new_lit = Literal(var_name);
            ids.push_back(new_lit.id);
            vars.push_back(var_name);

            cout << "Добавляем переменную " << var_name << " вида (" << i << ", " << j << ")" << (new_type == SINGLETON ? "-singleton" : "") << endl;

            vector<CNF *> new_lit_variants;

            for (CNF *cnf : cur)
            {
                auto new_vars = add_new_var(cnf, var_name, i, j, new_type);
                owner.adopt(new_vars);
                root_initialized = true;
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "addlit")
        {
            int i, j;
            string type;
            read_arguments(i, j, type);

            if (i < 1 || j < 1 || (type != "SINGLETON" && type != "ANY"))
            {
                cout << "Ожидается: addlit [i >= 1] [j >= 1] [SINGLETON | ANY]\n\n";
                continue;
            }

            LiteralDegType literal = {i, j, type == "SINGLETON" ? SINGLETON : ANY};
            validate_degree(i, j, literal.type);
            auto same_literal = [&](const LiteralDegType &other) {
                return other.i == literal.i && other.j == literal.j &&
                       other.type == literal.type;
            };

            if (find_if(POSSIBLE_LITERALS.begin(), POSSIBLE_LITERALS.end(), same_literal) ==
                POSSIBLE_LITERALS.end())
                POSSIBLE_LITERALS.push_back(literal);

            if (find_if(variants.begin(), variants.end(), same_literal) == variants.end())
                variants.push_back(literal);

            cout << "Добавлен тип (" << i << ", " << j << ")-"
                 << (literal.type == SINGLETON ? "singleton" : "any") << "\n\n";
            continue;
        }

        if (command == "addpos")
        {
            if (!root_initialized) throw invalid_argument("initialize the root with add first");
            string var_name;
            read_arguments(var_name);

            if (VAR2ID.count(var_name) != 0)
            {
                cout << "Это имя переменной уже занято. Попробуйте другое название переменной\n";
                continue;
            }

            Literal new_lit = Literal(var_name);
            ids.push_back(new_lit.id);
            vars.push_back(var_name);

            string l;

            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            read_command_line(l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            auto _posfunc = create_pos_func(need_lits, no_lits);

            vector<CNF *> new_lit_variants;

            for (CNF *cnf : cur)
            {
                auto new_vars = add_new_var_in_place(cnf, var_name, _posfunc, variants);
                owner.adopt(new_vars);
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "set")
        {
            read_arguments(C);
            if (!isfinite(C) || C <= 1) throw invalid_argument("target must exceed 1");

            cout << "C = " << C << "\n\n";

            continue;
        }

        if (command == "assumptions")
        {
            string value;
            read_arguments(value);
            if (value != "on" && value != "off")
            {
                cout << "Ожидается assumptions on или assumptions off\n\n";
                continue;
            }
            MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = value == "on";
            cout << "Named assumptions: "
                 << (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS ? "ON" : "OFF")
                 << "\n\n";
            continue;
        }

        if (command == "sv")
        {
            cout << "Введите булеву маску возможных литералов для добавления в следующем порядке (0 - не добавлять / 1 - добавить):\n";
            vector <LiteralDegType> new_pos_literals;
            const vector<LiteralDegType> &tmplte = POSSIBLE_LITERALS;

            for(LiteralDegType dt : tmplte)
            {
                cout << dt.i << " " << dt.j << " ";
                if (dt.type == LitType::SINGLETON)
                {
                    cout << "SINGLETON";
                }
                else if (dt.type == LitType::ANY)
                {
                    cout << "ANY";
                }
                cout << endl;
            }

            string msk;
            read_arguments(msk);

            if (msk.size() != tmplte.size() ||
                msk.find_first_not_of("01") != string::npos)
            {
                cout << "Ожидается маска из " << tmplte.size()
                     << " символов 0/1; список не изменён.\n\n";
                continue;
            }

            for(size_t i = 0; i < msk.size(); ++i)
            {
                if(msk[i] == '1')
                    new_pos_literals.push_back(tmplte[i]);
            }

            swap(new_pos_literals, variants);

            cout << "Сейчас в рассмотрении:\n";
            for(LiteralDegType lt : variants)
            {
                cout << "(" << lt.i << ", " << lt.j << ")";
                if(lt.type == SINGLETON)
                {
                    cout << "-singleton";
                }
                cout << endl;
            }
            continue;
        }   

        if (command == "setposfunc")
        {
            string l;

            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            read_command_line(l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            posfunc = create_pos_func(need_lits, no_lits);
            continue;
        }

        if (command == "simple_branch")
        {
            branch_epoch_universal(cur, ids, C, false, false);
            cout << endl;
            continue;
        }

        if (command == "xiao_branch")
        {
            int depth;

            read_arguments(depth);
            if (depth < 0) throw invalid_argument("depth must be nonnegative");

            branch_epoch_universal(cur, ids, C, false, true, depth);
            cout << endl;
            continue;
        }

        if (command == "branch")
        {
            branch_epoch_universal(cur, ids, C, true, false);
            cout << endl;
            continue;
        }

        if (command == "head")
        {
            int n;
            read_arguments(n);

            for (int i = 0; i < min((int)cur.size(), n); ++i)
            {
                print_cnf(*cur[i]);
                cout << endl;
            }

            continue;
        }

        if (command == "print")
        {
            int i;
            read_arguments(i);

            if (i < 0 || i >= (int)cur.size())
            {
                cout << "Формулы с индексом " << i
                     << " сейчас нет; осталось [" << cur.size()
                     << "] вариантов.\n\n";
                continue;
            }

            pretty_branch_print(vars, cur.at(i));
            cout << endl;

            ProofNode reg_node = cur.at(i)->branch(ids);
            ProofNode group_node = cur.at(i)->branch_group(ids, -1, false, C);
            ProofNode xiao_node = cur.at(i)->xiao_branch(1, "", C);

            vector<int> reg_branch = reg_node.vec;
            vector<int> group_branch = group_node.vec;
            vector<int> xiao_branch = xiao_node.vec;

            cout << "Regular Branch:\n";
            for (int r : reg_branch)
                cout << r << " ";

            cout << "\n|  " << branching_factor(reg_branch);
            cout << endl;

            cout << "Group Branch:\n";
            for (int r : group_branch)
                cout << r << " ";
            cout << "\n|  " << branching_factor(group_branch);
            cout << "\n\n";


            cout << "Xiao Branch (Depth = 1):\n";
            for (int r : xiao_branch)
                cout << r << " ";
            cout << "\n| " << branching_factor(xiao_branch);
            cout << "\n\n";

            cout << "Pos Func:\t";
            cout << posfunc(cur.at(i)) << "\n\n";

            continue;
        }

        if (command == "printall")
        {
            for (int i = 0; i < cur.size(); ++i)
            {
                pretty_branch_print(vars, cur.at(i));
                cout << endl;

                ProofNode reg_node = cur.at(i)->branch(ids);
                ProofNode group_node = cur.at(i)->branch_group(ids, -1, false, C);
                ProofNode xiao_node = cur.at(i)->xiao_branch(1, "", C);

                vector<int> reg_branch = reg_node.vec;
                vector<int> group_branch = group_node.vec;
                vector<int> xiao_branch = xiao_node.vec;

                cout << "Group Branch:\n";
                for (int r : group_branch)
                    cout << r << " ";
                cout << "\n|  " << branching_factor(group_branch);
                cout << "\n\n";

                cout << "Xiao Branch (Depth = 1):\n";
                for (int r : xiao_branch)
                    cout << r << " ";
                cout << "\n| " << branching_factor(xiao_branch);
                cout << "\n\n";
                
                cout << "=================================================\n\n";

            }

            continue;
        }


        if (command == "printworst")
        {
            long double worst = -1;
            int worst_ind = -1;
            for (int i = 0; i < cur.size(); ++i)
            {
                long double gfactor = branching_weight(cur.at(i)->branch_group(ids, -1, false, C).vec, C);
                
                if (gfactor > worst)
                {
                    worst = gfactor;
                    worst_ind = i;
                }
            }

            cout << "Formula: " << worst_ind << '\n';
            cout << "| W_q = " << worst << "\n\n";

            continue;
        }

        if (command == "stats")
        {
            if (cur.empty())
            {
                cout << "В данный момент нет вариантов для анализа.\n\n";
                continue;
            }

            double min_bf = 1e18; // Достаточно большое число для инициализации минимума
            double max_bf = -1.0;

            // vector <int> mn_branch;
            // vector <int> mx_branch;

            for (CNF *cnf : cur)
            {

                // Берем минимум между групповым ветвлением и ветвлением xiao
                ProofNode grouped = cnf->branch_group(ids, -1, false, C);
                ProofNode xiao = cnf->xiao_branch(1, "", C);
                double current_bf = branching_weight(grouped.vec, C) < branching_weight(xiao.vec, C)
                                        ? grouped.tau : xiao.tau;

                min_bf = min(min_bf, current_bf);
                max_bf = max(max_bf, current_bf);
            }

            cout << "Статистика по " << cur.size() << " вариантам:\n";
            cout << "Минимальный Branching Factor:  " << min_bf << "\n";
            cout << "Максимальный Branching Factor: " << max_bf << "\n\n";

            continue;
        }

        if (command == "cache_stats")
        {
            auto stats = strategy_cache_stats();
            cout << "Strategy cache: hits=" << stats.hits
                 << ", misses=" << stats.misses
                 << ", entries=" << stats.entries
                 << ", evictions=" << stats.evictions << "\n\n";
            continue;
        }

        if (command == "empty_divide")
        {
            int i;
            read_arguments(i);

            if (i == -1)
            {
                vector<CNF *> next_cur;
                int success_count = 0;
                
                for (CNF *cnf : cur)
                {
                    DivideResult res = empty_divide(cnf, C);
                    if (res.cnf_empty != nullptr)
                    {
                        owner.adopt({res.cnf_empty, res.cnf_not_empty});
                        next_cur.push_back(res.cnf_empty);
                        next_cur.push_back(res.cnf_not_empty);
                        success_count++;
                    }
                    else
                    {
                        next_cur.push_back(cnf);
                    }
                }
                swap(cur, next_cur);
                cout << "empty_divide успешно применен к " << success_count << " формулам.\n";
                cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
            }
            else
            {
                cout << "Извините, пока что empty_divide работает только с -1\n\n";
                // if (i >= 0 && i < (int)cur.size())
                // {
                //     pair<CNF *, CNF *> res = empty_divide(cur[i]);
                //     if (res.first != nullptr)
                //     {
                //         // Удаляем старую формулу и на её место вставляем две новые
                //         CNF* old_cnf = cur[i];
                //         cur.erase(cur.begin() + i);
                //         cur.insert(cur.begin() + i, res.second);
                //         cur.insert(cur.begin() + i, res.first);
                //         // delete old_cnf; // Не забывайте про освобождение памяти

                //         cout << "empty_divide успешно применен к формуле " << i << ".\n";
                //         cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
                //     }
                //     else
                //     {
                //         cout << "В формуле " << i << " не найдено литералов '?' для разбиения.\n\n";
                //     }
                // }
                // else
                // {
                //     cout << "Неверный индекс формулы.\n\n";
                // }
            }
            continue;
        }

        if (command == "factor")
        {
            std::string l;
            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            vector<int> C_branch;

            while (getline(ss, token, ' '))
            {
                if (!token.empty()) C_branch.push_back(stoi(token));
            }
            cout << endl;

            cout << setprecision(10) << branching_factor(C_branch) << endl;

            continue;
        }

        if (command == "target")
        {
            int i;
            read_arguments(i);

            cur = {cur.at(i)};
            cout << "\n\n";
            continue;
        }

        if (command == "drop")
        {
            int i;
            read_arguments(i);

            if (i < 0 || i >= (int)cur.size()) throw out_of_range("drop index out of range");
            cur.erase(cur.begin() + i);
            
            cout << "Done.\n\n";
            continue;
        }

        if (command == "help")
        {
            print_help_universal();
            continue;
        }

        if (command == "exit")
        {
            break;
        }

        cout << "Команда [" << command << "] не распознана\n";
    }
}

// -----------------------------------------------------------------------
// Тест: проверяет корректность всех разбиений из groups3.txt
//
// Каждое разбиение — строка из 8 символов (цифр), где s[i] — номер
// группы (класс) для i-й подстановки {x=бит0, y=бит1, z=бит2}.
// Для каждой группы вызываем check_group_validity с k=3.
// -----------------------------------------------------------------------
void test_groups3_validity()
{
    const int k = 3;  // Три переменных ветвления
    const int total_masks = 1 << k; // 8 подстановок

    if (valid_3_partitions.empty())
    {
        cout << "[SKIP] valid_3_partitions не загружены (запустите preprocess())\n";
        return;
    }

    int total   = (int)valid_3_partitions.size();
    int ok_cnt  = 0;
    int bad_cnt = 0;

    cout << "Проверяем " << total << " разбиений из groups3.txt...\n";

    for (int pi = 0; pi < total; ++pi)
    {
        const string& part = valid_3_partitions[pi];

        if ((int)part.size() != total_masks)
        {
            cout << "[BAD #" << pi << "] Строка \"" << part
                 << "\" имеет неверную длину " << part.size()
                 << " (ожидается " << total_masks << ")\n";
            bad_cnt++;
            continue;
        }

        // Определяем, сколько классов и какие маски в каждом
        int max_class = 0;
        for (char ch : part)
            max_class = max(max_class, (int)(ch - '0'));

        bool partition_ok = true;

        for (int cls = 0; cls <= max_class; ++cls)
        {
            // Собираем маски этого класса
            vector<int> group_masks;
            for (int mask = 0; mask < total_masks; ++mask)
                if ((int)(part[mask] - '0') == cls)
                    group_masks.push_back(mask);

            if (group_masks.empty())
                continue; // пропуск несуществующего класса

            string diag;
            bool group_ok = check_group_validity(group_masks, k, diag);

            if (!group_ok)
            {
                if (partition_ok)
                {
                    // Первая ошибка в этом разбиении — выводим заголовок
                    cout << "\n[BAD #" << pi << "] Разбиение: \"" << part << "\"\n";
                }
                partition_ok = false;

                // Маски в группе с расшифровкой (xyz — бит0=x, бит1=y, бит2=z)
                cout << "  Класс " << cls << " (маски:";
                for (int m : group_masks)
                {
                    cout << " " << ((m >> 2) & 1) << ((m >> 1) & 1) << (m & 1);
                }
                cout << ")\n";
                cout << "  Причина: " << diag << "\n";
            }
        }

        if (partition_ok)
            ok_cnt++;
        else
            bad_cnt++;
    }

    cout << "\n=== Итог: " << ok_cnt << "/" << total << " разбиений корректны";
    if (bad_cnt == 0)
        cout << " — всё OK ✓\n";
    else
        cout << ", " << bad_cnt << " НЕКОРРЕКТНЫХ ✗\n";
}
