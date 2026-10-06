#include "group_cover.h"
#include "cnf.h"

#include <algorithm>
#include <cmath>
#include <iterator>
#include <map>
#include <stdexcept>

void enumerate_substitution_groups(
    int variable_count,
    const std::function<void(const std::vector<int>&)> &visit)
{
    if (variable_count < 0 || variable_count > MAX_MASK_BITS)
        throw std::invalid_argument("unsupported substitution variable count");
    std::vector<int> columns(variable_count);
    std::function<void(int, int)> generate = [&](int column, int free_count) {
        if (column == variable_count)
        {
            std::vector<int> rows;
            for (int values = 0; values < (1 << free_count); ++values)
            {
                int row = 0;
                for (int j = 0; j < variable_count; ++j)
                {
                    int code = columns[j];
                    bool value = code == -2 ||
                        (code >= 0 && (((values >> (code / 2)) & 1) ^ (code & 1)));
                    if (value) row |= 1 << j;
                }
                rows.push_back(row);
            }
            std::sort(rows.begin(), rows.end());
            visit(rows);
            return;
        }
        // Constants, then either polarity of an earlier representative.
        for (int code = -2; code < 2 * free_count; ++code)
        {
            columns[column] = code;
            generate(column + 1, free_count);
        }
        // Name a new free variable by its first occurrence, with positive sign.
        // This removes all permutations and sign renamings of representatives.
        if ((1 << (free_count + 1)) <= MAX_MASK_BITS)
        {
            columns[column] = 2 * free_count;
            generate(column + 1, free_count + 1);
        }
    };
    generate(0, 0);
}

GroupCover minimum_group_cover(int assignment_count,
                              const std::vector<WeightedGroup> &candidates,
                              int max_groups)
{
    if (assignment_count < 0 || max_groups < -1)
        throw std::invalid_argument("invalid cover size or group limit");
    std::vector<std::vector<int>> covers(candidates.size());
    // Equal coverage needs only its cheapest group, irrespective of its image.
    std::map<std::vector<int>, int> best_for_coverage;
    for (int i = 0; i < (int)candidates.size(); ++i)
    {
        if (!std::isfinite(candidates[i].weight) || candidates[i].weight < 0)
            throw std::invalid_argument("group weight must be finite and nonnegative");
        covers[i] = candidates[i].coverage;
        std::sort(covers[i].begin(), covers[i].end());
        covers[i].erase(std::unique(covers[i].begin(), covers[i].end()), covers[i].end());
        for (int row : covers[i])
            if (row < 0 || row >= assignment_count)
                throw std::invalid_argument("group coverage outside assignment universe");
        if (covers[i].empty()) continue;
        auto [it, inserted] = best_for_coverage.emplace(covers[i], i);
        if (!inserted && candidates[i].weight < candidates[it->second].weight)
            it->second = i;
    }
    std::vector<std::vector<int>> covering(assignment_count);
    for (const auto &[rows, candidate] : best_for_coverage)
        for (int row : rows) covering[row].push_back(candidate);

    struct Entry { long double weight; int choice; };
    using State = std::pair<std::vector<int>, int>;
    std::map<State, Entry> memo;
    auto remove_covered = [&](const std::vector<int> &remaining, int group) {
        std::vector<int> next;
        std::set_difference(remaining.begin(), remaining.end(),
                            covers[group].begin(), covers[group].end(),
                            std::back_inserter(next));
        return next;
    };
    const long double infinity = std::numeric_limits<long double>::infinity();
    std::function<long double(const std::vector<int>&, int)> solve =
        [&](const std::vector<int> &remaining, int budget) -> long double {
        if (remaining.empty()) return 0;
        if (budget == 0) return infinity;
        State state{remaining, budget};
        auto existing = memo.find(state);
        if (existing != memo.end()) return existing->second.weight;
        Entry best{infinity, -1};
        // Every cover contains a group covering the first uncovered row.
        // Each transition removes that row, so overlap cannot create a cycle.
        for (int group : covering[remaining.front()])
        {
            auto next = remove_covered(remaining, group);
            long double weight = candidates[group].weight +
                solve(next, budget < 0 ? -1 : budget - 1);
            if (weight < best.weight) best = {weight, group};
        }
        memo.emplace(std::move(state), best);
        return best.weight;
    };
    std::vector<int> remaining;
    for (int i = 0; i < assignment_count; ++i) remaining.push_back(i);
    int budget = max_groups < 0 ? -1 : std::min(max_groups, assignment_count);
    GroupCover result;
    result.weight = solve(remaining, budget);
    if (!std::isfinite(result.weight)) return result;
    while (!remaining.empty())
    {
        int choice = memo.at({remaining, budget}).choice;
        result.groups.push_back(choice);
        remaining = remove_covered(remaining, choice);
        if (budget >= 0) --budget;
    }
    return result;
}
