#pragma once

#include "cnf.h"
#include <cstddef>

enum class StrategySearchKind { Variable, Residual };

struct StrategyCacheStats {
    std::size_t hits = 0;
    std::size_t misses = 0;
    std::size_t evictions = 0;
    std::size_t entries = 0;
};

// Process-local and bounded. Keys retain variable IDs and clause order,
// and normalize only tail IDs, preserving their types and sharing.
ProofNode cached_strategy_search(const CNF &formula, StrategySearchKind kind,
                                int depth, double q,
                                const std::function<ProofNode()> &search);
// Formula-based entry point shared by current and future group enumerators.
ProofNode analyze_residual(const CNF &formula, int depth, double q);
StrategyCacheStats strategy_cache_stats();
void clear_strategy_cache();
void set_strategy_cache_enabled(bool enabled);
