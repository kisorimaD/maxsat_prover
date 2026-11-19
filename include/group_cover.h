#pragma once

#include <functional>
#include <limits>
#include <vector>

// Images of substitutions by constants and signed representative variables.
// Each representable group is visited once, in a deterministic order.
void enumerate_substitution_groups(
    int variable_count,
    const std::function<void(const std::vector<int>&)> &visit);

struct WeightedGroup {
    std::vector<int> coverage; // indices in the undominated assignment universe
    long double weight;
};

struct GroupCover {
    long double weight = std::numeric_limits<long double>::infinity();
    std::vector<int> groups; // indices in the input candidate list
};

// Exact weighted set cover. Groups may overlap.
GroupCover minimum_group_cover(int assignment_count,
                              const std::vector<WeightedGroup> &candidates);
