#include "lemmas.h"
#include "cnf.h"
#include "cert_logger.h"

#include <algorithm>
#include <cstdlib>
#include <map>
#include <iostream>

LemmaExportSettings lemma_export_settings;

namespace {
std::map<long long, ProofNode> session_candidates;
}

bool lemma_export_enabled() { return !lemma_export_settings.output_file.empty(); }

void remember_lemma_candidate(long long node_id, const ProofNode &proof)
{
    if (!lemma_export_enabled()) return;
    auto previous = session_candidates.find(node_id);
    if (previous == session_candidates.end() ||
        branching_weight(proof.vec, lemma_export_settings.q) <
        branching_weight(previous->second.vec, lemma_export_settings.q) ||
        (branching_weight(proof.vec,lemma_export_settings.q)==branching_weight(previous->second.vec,lemma_export_settings.q) &&
         proof_establishes_progress(proof) && !proof_establishes_progress(previous->second)))
        session_candidates[node_id] = proof;
}

void retain_lemma_candidates(const std::vector<CNF*> &frontier)
{
    if (!lemma_export_enabled()) return;
    std::set<long long> live;
    for (CNF *formula : frontier) live.insert(formula->node_id);
    for (auto it = session_candidates.begin(); it != session_candidates.end(); )
        if (!live.count(it->first)) it = session_candidates.erase(it);
        else ++it;
}

void finish_lemma_session(const std::vector<CNF*> &frontier, const std::vector<int> &variables)
{
    if (!lemma_export_enabled()) return;
    for (CNF *formula : frontier)
    {
        // Cover even untouched frontier leaves. Keep the best strategy found
        // during the session; do not silently rerun a more expensive search.
        remember_lemma_candidate(formula->node_id, formula->branch(variables));
        global_logger.log_proof_tree(formula->node_id, session_candidates.at(formula->node_id), formula->active_tail_exclusions());
    }
    session_candidates.clear();
    std::cout << "Lemma session ready for assembly: q=" << lemma_export_settings.target
              << ", output=" << lemma_export_settings.output_file << '\n';
}

namespace {
using Matcher = std::vector<LemmaApplication> (*)(const CNF&);

std::vector<LemmaApplication> match_step51(const CNF &formula)
{
    std::vector<LemmaApplication> result;
    for (const auto &[id, stats] : analyze_formula(formula))
    {
        bool positive = stats.pos_count == 3 && stats.neg_count == 2;
        bool negative = stats.neg_count == 3 && stats.pos_count == 2;
        if (!positive && !negative) continue;
        // A tautological clause would count in both occurrence lists and
        // cannot represent two distinct clauses of the lemma template.
        if (std::any_of(stats.pos_indices.begin(), stats.pos_indices.end(),
            [&](int clause) {
                return std::find(stats.neg_indices.begin(), stats.neg_indices.end(), clause)
                       != stats.neg_indices.end();
            })) continue;
        const auto &minority = positive ? stats.neg_indices : stats.pos_indices;
        for (int index : minority)
        {
            const Clause *clause = formula.clauses[index];
            if (!clause->tail_atoms.empty() || clause->lits.size() != 1) continue;
            const Literal *literal = *clause->lits.begin();
            if (literal->id != id || is_any_unknown_literal(literal)) continue;
            result.push_back({"step5.1", {positive ? id : -id}, {index}, {4, 2}});
            break; // Identical guarantee for either minority unit clause.
        }
    }
    return result;
}

// Adding a proved lemma adds a matcher here and a proof definition to the
// assembler's library. Search/grouping consume the same application object.
const Matcher proved_lemmas[] = {match_step51};
}

std::vector<LemmaApplication> find_proved_lemma_applications(const CNF &formula, double q, int step6_context)
{
    std::vector<LemmaApplication> result;
    for (Matcher matcher : proved_lemmas)
    {
        auto applications = matcher(formula);
        result.insert(result.end(), applications.begin(), applications.end());
    }
    auto saved = find_saved_lemma_applications(formula, q, step6_context);
    result.insert(result.end(), saved.begin(), saved.end());
    return result;
}

ProofNode lemma_application_leaf(const CNF &formula, const LemmaApplication &application)
{
    ProofNode result(application.vector);
    result.type = "lemma";
    result.rule = application.id;
    result.pivot_id = std::abs(application.role_literals.at(0));
    result.formula_snapshot = formula.get_cert_snapshot();
    result.lemma_application = std::make_shared<const LemmaApplication>(application);
    return result;
}
