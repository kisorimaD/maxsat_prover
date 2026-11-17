#pragma once

#include <string>
#include <vector>
#include <array>
#include <cstdint>

class CNF;
struct ProofNode;
struct LiteralDegType;

// A proof-backed lemma application. Roles are signed literals; witnesses are
// indices in the producer's clause order. No formula/tail IDs are duplicated,
// so residual-cache tail renaming leaves this immutable metadata unchanged.
struct LemmaApplication {
    std::string id;
    std::vector<int> role_literals;
    std::vector<int> witness_clauses;
    std::vector<int> vector;
    std::string definition_digest;
    std::vector<std::array<int, 3>> degree_scope;
};

std::vector<LemmaApplication> find_proved_lemma_applications(const CNF &formula, double q = 1.2873, int step6_context = -1);
ProofNode lemma_application_leaf(const CNF &formula, const LemmaApplication &application);

// Opt-in session export. Candidate storage is absent in ordinary sessions.
struct LemmaExportSettings {
    std::string target;
    std::string output_file;
    double q = 0;
};
extern LemmaExportSettings lemma_export_settings;
bool lemma_export_enabled();
void remember_lemma_candidate(long long node_id, const ProofNode &proof);
void retain_lemma_candidates(const std::vector<CNF*> &frontier);
void finish_lemma_session(const std::vector<CNF*> &frontier, const std::vector<int> &variables);

struct SavedLemmaSource { std::string id, digest, path; };
struct SavedLemmaStats { std::size_t loaded = 0, attempts = 0, matches = 0; };
void load_saved_lemmas(const std::vector<std::string> &files);
const std::vector<SavedLemmaSource> &saved_lemma_sources();
SavedLemmaStats saved_lemma_stats();
void set_lemma_search_target(const std::string &decimal);
void set_lemma_degree_scope(const std::vector<LiteralDegType> &degrees);
bool lemma_degree_scope_is_step6();
std::vector<std::array<int, 3>> lemma_current_degree_scope();
std::uint64_t saved_lemma_policy_revision();
std::vector<LemmaApplication> find_saved_lemma_applications(const CNF &formula, double q, int step6_context = -1);
