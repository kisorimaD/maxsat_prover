#pragma once

#include "cnf.h"
#include <cstddef>

struct StrategyCacheStats {
    std::size_t hits = 0;
    std::size_t misses = 0;
    std::size_t evictions = 0;
    std::size_t entries = 0;
};

// Process-local and bounded. Keys retain variable IDs and clause order,
// and normalize only tail IDs, preserving their types and sharing.
ProofNode cached_strategy_search(const CNF &formula, double q,
                                const std::function<ProofNode()> &search);
StrategyCacheStats strategy_cache_stats();
void clear_strategy_cache();
void set_strategy_cache_enabled(bool enabled);
