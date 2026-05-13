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
    void log_add_variable(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int pos_deg, int neg_deg, const std::vector<long long>& children_ids);
    
    // Логирование целевого макро-добавления (addpos)
    void log_addpos(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int target_pos, const std::vector<long long>& children_ids);
    
    // Логирование макро-разделения (empty_divide)
    void log_divide(long long parent_id, const std::vector<std::vector<int>>& snap, int target_idx, long long child_empty, long long child_not_empty);
    
    // Логирование терминального микро-доказательства
    void log_proof_tree(long long parent_id, const ProofNode& root_node);

private:
    std::string formula_to_json(const std::vector<std::vector<int>>& snap);
    std::string proof_node_to_json(const ProofNode& node);
};

extern std::ofstream out;

extern CertLogger global_logger;