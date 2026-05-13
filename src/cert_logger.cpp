#include "cert_logger.h"
#include <sstream>
#include <iostream>
#include <fstream>

// Глобальный экземпляр логгера
CertLogger global_logger;
std::ofstream out;

void CertLogger::init(const std::string& filename) {
    out.open(filename, std::ios::out | std::ios::trunc);
    if (!out.is_open()) {
        std::cerr << "Не удалось открыть файл для логов: " << filename << std::endl;
    }
}

void CertLogger::close() {
    if (out.is_open()) {
        out.close();
    }
}

// Конвертация снимка формулы в строку формата JSON (массив массивов)
std::string CertLogger::formula_to_json(const std::vector<std::vector<int>>& snap) {
    std::ostringstream ss;
    ss << "[";
    for (size_t i = 0; i < snap.size(); ++i) {
        ss << "[";
        for (size_t j = 0; j < snap[i].size(); ++j) {
            ss << snap[i][j];
            if (j + 1 < snap[i].size()) ss << ", ";
        }
        ss << "]";
        if (i + 1 < snap.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
}

void CertLogger::log_add_variable(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int pos_deg, int neg_deg, const std::vector<long long>& children_ids) {
    if (!out.is_open()) return;

    std::ostringstream ss;
    ss << "{\"parent_id\": " << parent_id << ", "
       << "\"type\": \"add_variable\", "
       << "\"formula\": " << formula_to_json(snap) << ", "
       << "\"added_variable_id\": " << var_id << ", "
       << "\"pos_deg\": " << pos_deg << ", "
       << "\"neg_deg\": " << neg_deg << ", "
       << "\"children_ids\": [";
    for (size_t i = 0; i < children_ids.size(); ++i) {
        ss << children_ids[i];
        if (i + 1 < children_ids.size()) ss << ", ";
    }
    ss << "]}\n";
    out << ss.str();
    out.flush();
}

void CertLogger::log_addpos(long long parent_id, const std::vector<std::vector<int>>& snap, int var_id, int target_pos, const std::vector<long long>& children_ids) {
    if (!out.is_open()) return;

    std::ostringstream ss;
    ss << "{\"parent_id\": " << parent_id << ", "
       << "\"type\": \"addpos\", "
       << "\"formula\": " << formula_to_json(snap) << ", "
       << "\"added_variable_id\": " << var_id << ", "
       << "\"target_clause_idx\": " << target_pos << ", "
       << "\"children_ids\": [";
    for (size_t i = 0; i < children_ids.size(); ++i) {
        ss << children_ids[i];
        if (i + 1 < children_ids.size()) ss << ", ";
    }
    ss << "]}\n";
    out << ss.str();
    out.flush();
}

// Логирование операции разделения клозы (макро-уровень)
void CertLogger::log_divide(long long parent_id, const std::vector<std::vector<int>>& snap, int target_idx, long long child_empty, long long child_not_empty) {
    if (!out.is_open()) return;

    std::ostringstream ss;
    ss << "{\"parent_id\": " << parent_id << ", "
       << "\"type\": \"macro_divide_clause\", "
       << "\"formula\": " << formula_to_json(snap) << ", "
       << "\"target_clause_idx\": " << target_idx << ", "
       << "\"children_ids\": [" << child_empty << ", " << child_not_empty << "]}\n";
       
    out << ss.str();
    out.flush();
}

// Рекурсивный обход терминального дерева (микро-уровень)
std::string CertLogger::proof_node_to_json(const ProofNode& node) {
    std::ostringstream ss;
    ss << "{";
    
    // Lean 4 ожидает node_id как строку
    ss << "\"node_id\": \"micro_node\", "; 
    ss << "\"type\": \"" << node.type << "\", ";
    ss << "\"formula\": " << formula_to_json(node.formula_snapshot) << ", ";

    // Специфичные поля в зависимости от типа узла (согласно test.Lean)
    if (node.type == "leaf") {
        ss << "\"tau\": " << node.tau << ", ";
        ss << "\"vector\": [";
        for (size_t i = 0; i < node.vec.size(); ++i) {
            ss << node.vec[i];
            if (i + 1 < node.vec.size()) ss << ", ";
        }
        ss << "], ";
    } 
    else if (node.type == "divide_clause") {
        ss << "\"target_clause_idx\": " << node.target_clause_idx << ", ";
    } 
    else if (node.type == "branch") {
        ss << "\"branching_variable\": " << node.pivot_id << ", ";
    } 
    else if (node.type == "reduction") {
        ss << "\"rule\": \"" << node.rule << "\", ";
        ss << "\"pivot_id\": " << node.pivot_id << ", ";
    } 
    else if (node.type == "add_variable") {
        // Если вдруг add_variable окажется внутри микро-дерева
        ss << "\"added_variable_id\": " << node.pivot_id << ", ";
        ss << "\"pos_deg\": 0, "; // Дефолтные значения, если их нет в C++ ProofNode
        ss << "\"neg_deg\": 0, ";
    }

    // Рекурсивный вызов для потомков
    ss << "\"children\": [";
    for (size_t i = 0; i < node.children.size(); ++i) {
        ss << proof_node_to_json(node.children[i]);
        if (i + 1 < node.children.size()) ss << ", ";
    }
    ss << "]";

    ss << "}";
    return ss.str();
}

// Логирование корня доказанного микро-дерева
void CertLogger::log_proof_tree(long long parent_id, const ProofNode& root_node) {
    if (!out.is_open()) return;

    std::ostringstream ss;
    ss << "{\"parent_id\": " << parent_id << ", "
       << "\"type\": \"proof_tree\", "
       << "\"proof_node\": " << proof_node_to_json(root_node) << "}\n";
       
    out << ss.str();
    out.flush();
}