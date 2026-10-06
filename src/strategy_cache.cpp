#include "strategy_cache.h"

#include <cmath>
#include <deque>
#include <stdexcept>
#include <unordered_map>

namespace {
constexpr std::size_t MAX_ENTRIES = 2048;
constexpr std::size_t MAX_PROOF_NODES = 256;
constexpr std::size_t MAX_TOTAL_NODES = 32768;

struct Entry {
    ProofNode proof;
    std::size_t nodes;
};
std::unordered_map<std::string, Entry> entries;
std::deque<std::string> insertion_order;
std::size_t retained_nodes = 0;
StrategyCacheStats counters;
bool cache_enabled = true;

template<class T>
void append(std::string &key, const T &value)
{
    key.append(reinterpret_cast<const char *>(&value), sizeof(value));
}

int map_tail(int value, const std::map<int, int> &mapping)
{
    if (value < SNAP_TAIL_ANY_BASE) return value;
    int base = value >= SNAP_TAIL_NONEMPTY_BASE
                   ? SNAP_TAIL_NONEMPTY_BASE : SNAP_TAIL_ANY_BASE;
    return base + mapping.at(value - base);
}

void map_formula(std::vector<std::vector<int>> &formula,
                 const std::map<int, int> &mapping)
{
    for (auto &clause : formula)
        for (int &literal : clause) literal = map_tail(literal, mapping);
}

// Deep-copy proofs: callers can mutate their result without altering the cache.
ProofNode map_proof(const ProofNode &source, const std::map<int, int> &mapping)
{
    ProofNode result = source;
    map_formula(result.formula_snapshot, mapping);
    for (auto &child : result.children) child = map_proof(child, mapping);
    for (auto &alternative : result.alternatives)
        if (alternative.proof)
            alternative.proof = std::make_shared<ProofNode>(
                map_proof(*alternative.proof, mapping));
    for (auto &witness : result.group_witnesses)
    {
        if (witness.residual_proof)
            witness.residual_proof = std::make_shared<ProofNode>(
                map_proof(*witness.residual_proof, mapping));
    }
    return result;
}

std::size_t proof_nodes(const ProofNode &proof)
{
    std::size_t count = 1;
    for (const auto &child : proof.children) count += proof_nodes(child);
    for (const auto &alternative : proof.alternatives)
        if (alternative.proof) count += proof_nodes(*alternative.proof);
    for (const auto &witness : proof.group_witnesses)
        if (witness.residual_proof) count += proof_nodes(*witness.residual_proof);
    return count;
}
} // namespace

void clear_strategy_cache()
{
    entries.clear();
    insertion_order.clear();
    retained_nodes = 0;
    counters = {};
}

void set_strategy_cache_enabled(bool enabled)
{
    clear_strategy_cache();
    cache_enabled = enabled;
}

StrategyCacheStats strategy_cache_stats()
{
    auto stats = counters;
    stats.entries = entries.size();
    return stats;
}

ProofNode cached_strategy_search(const CNF &formula, StrategySearchKind kind,
                                int depth, double q,
                                const std::function<ProofNode()> &search)
{
    if (depth < 0 || !std::isfinite(q) || q <= 1.0)
        throw std::invalid_argument("invalid strategy search depth or target");
    if (!cache_enabled) return search();

    std::string key;
    append(key, kind);
    append(key, depth);
    append(key, q);
    append(key, MaxSATSettings.MAXIMUM_CLAUSE_SIZE);
    append(key, MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS);
    std::map<int, int> to_canonical, from_canonical;
    auto snapshot = formula.get_cert_snapshot();
    append(key, snapshot.size());
    for (std::size_t index = 0; index < snapshot.size(); ++index)
    {
        const auto &clause = snapshot[index];
        // Search also inspects wildcard markers, so retain them even when
        // two representations have the same certificate snapshot.
        int markers = (formula.clauses[index]->lits.count(&UNKNOWN_LITERAL) ? 1 : 0) |
                      (formula.clauses[index]->lits.count(&UNKNOWN_NOT_EMPTY_LITERAL) ? 2 : 0);
        append(key, markers);
        append(key, clause.size());
        for (int literal : clause)
        {
            if (literal >= SNAP_TAIL_ANY_BASE)
            {
                int base = literal >= SNAP_TAIL_NONEMPTY_BASE
                               ? SNAP_TAIL_NONEMPTY_BASE : SNAP_TAIL_ANY_BASE;
                int tail = literal - base;
                if (!to_canonical.count(tail))
                {
                    int canonical = static_cast<int>(to_canonical.size());
                    to_canonical[tail] = canonical;
                    from_canonical[canonical] = tail;
                }
                literal = base + to_canonical.at(tail);
            }
            append(key, literal);
        }
    }
    auto cached = entries.find(key);
    if (cached != entries.end())
    {
        ++counters.hits;
        return map_proof(cached->second.proof, from_canonical);
    }
    ++counters.misses;
    ProofNode proof = search();
    std::size_t nodes = proof_nodes(proof);
    if (nodes <= MAX_PROOF_NODES)
    {
        while (entries.size() >= MAX_ENTRIES || retained_nodes + nodes > MAX_TOTAL_NODES)
        {
            auto oldest = entries.find(insertion_order.front());
            retained_nodes -= oldest->second.nodes;
            entries.erase(oldest);
            insertion_order.pop_front();
            ++counters.evictions;
        }
        entries.emplace(key, Entry{map_proof(proof, to_canonical), nodes});
        insertion_order.push_back(std::move(key));
        retained_nodes += nodes;
    }
    return proof;
}

ProofNode analyze_residual(const CNF &formula, int depth, double q)
{
    return cached_strategy_search(formula, StrategySearchKind::Residual, depth, q, [&] {
        ReductionFixpoint reduced = reduce_to_fixpoint(formula);
        std::unique_ptr<CNF, decltype(&destroy_cnf)> owner(reduced.cnf, destroy_cnf);
        ProofNode child({0});
        child.formula_snapshot = reduced.cnf->get_cert_snapshot();
        if (reduced.total_decrease == 0)
            child = reduced.cnf->xiao_branch(depth, "", q);
        for (auto it = reduced.steps.rbegin(); it != reduced.steps.rend(); ++it)
        {
            ProofNode parent;
            parent.type = "reduction";
            parent.rule = it->rule;
            parent.pivot_id = it->pivot_id;
            parent.formula_snapshot = it->formula_snapshot;
            parent.rr_witness_clauses = it->witness_clauses;
            parent.vec = child.vec;
            for (int &decrease : parent.vec) decrease += it->decrease;
            parent.tau = branching_factor(parent.vec);
            parent.children.push_back(std::move(child));
            child = std::move(parent);
        }
        return child;
    });
}
