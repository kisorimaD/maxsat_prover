#pragma once
#include "cnf.h"
#include <string>
#include <vector>
#include <fstream>


class CertLogger {
public:
    void init(const std::string& filename);
    void close();

    // Логирование операции добавления переменной с известными степенями
    void log_add_variable(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int pos_deg, int neg_deg, LitType type, const std::vector<long long>& children_ids);
    
    // Логирование целевого макро-добавления (addpos)
    void log_addpos(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int target_pos, const std::vector<LiteralDegType>& degrees, const std::vector<long long>& children_ids, const TailExclusions &exclusions = {});
    void log_expose_type(const CNF &parent, int variable, int clause,
                         LiteralDegType degree, const vector<LiteralDegType> &scope,
                         const vector<long long> &children);
    
    // Логирование макро-разделения (empty_divide)
    void log_divide(long long parent_id, const std::vector<std::vector<int>>& snap, int target_idx, long long child_empty, long long child_not_empty, const TailExclusions &exclusions = {});
    
    // Логирование терминального микро-доказательства
    void log_proof_tree(long long parent_id, const ProofNode& root_node, const TailExclusions &exclusions = {});

    // Discard selected refinements before re-solving their parent formulas.
    void log_rollback(const std::vector<long long>& parent_ids);

    // Serialize a strategy fragment without opening or changing a log file.
    std::string serialize_proof(const ProofNode& root_node);
    std::string serialize_state(const CNF &formula);

private:
    std::string formula_to_json(const std::vector<std::vector<int>>& snap);
    std::string proof_node_to_json(const ProofNode& node);
};

extern std::ofstream out;

extern CertLogger global_logger;
