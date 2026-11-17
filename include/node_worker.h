#pragma once
#include <string>
#include <vector>

// Versioned stdin protocol used by global_search, with JSON-only stdout.
int run_node_worker(const std::vector<std::string> &lemma_files);
