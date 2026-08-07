#include "cert_logger.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>

CertLogger global_logger;
std::ofstream out;

void CertLogger::init(const std::string &filename)
{
    out.open(filename, std::ios::out | std::ios::trunc);
    if (!out.is_open())
        std::cerr << "Не удалось открыть файл для логов: " << filename << '\n';
}

void CertLogger::close()
{
    if (out.is_open()) out.close();
}

std::string CertLogger::formula_to_json(
    const std::vector<std::vector<int>> &snapshot)
{
    std::ostringstream ss;
    ss << '[';
    for (size_t i = 0; i < snapshot.size(); ++i)
    {
        ss << '[';
        for (size_t j = 0; j < snapshot[i].size(); ++j)
        {
            if (j) ss << ',';
            int value = snapshot[i][j];
            if (value >= SNAP_TAIL_NONEMPTY_BASE)
                ss << "{\"tail\":" << (value - SNAP_TAIL_NONEMPTY_BASE)
                   << ",\"kind\":\"nonempty\"}";
            else if (value >= SNAP_TAIL_ANY_BASE)
                ss << "{\"tail\":" << (value - SNAP_TAIL_ANY_BASE)
                   << ",\"kind\":\"any\"}";
            else
                ss << value;
        }
        ss << ']';
        if (i + 1 != snapshot.size()) ss << ',';
    }
    ss << ']';
    return ss.str();
}

namespace
{
void write_ids(std::ostringstream &ss, const std::vector<long long> &ids)
{
    ss << '[';
    for (size_t i = 0; i < ids.size(); ++i)
    {
        if (i) ss << ',';
        ss << ids[i];
    }
    ss << ']';
}
}

void CertLogger::log_add_variable(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int var_id, int pos_deg, int neg_deg,
    const std::vector<long long> &children_ids)
{
    if (!out.is_open()) return;
    std::ostringstream ss;
    ss << "{\"node_id\":" << parent_id
       << ",\"kind\":\"refine\",\"rule\":\"expose_variable\""
       << ",\"formula\":" << formula_to_json(snapshot)
       << ",\"variable\":" << var_id
       << ",\"positive\":" << pos_deg
       << ",\"negative\":" << neg_deg
       << ",\"singleton\":" << ((pos_deg == 1 || neg_deg == 1) ? "true" : "false")
       << ",\"children_ids\":";
    write_ids(ss, children_ids);
    ss << "}\n";
    out << ss.str();
}

void CertLogger::log_addpos(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int var_id, int target_pos, const std::vector<long long> &children_ids)
{
    if (!out.is_open()) return;
    std::ostringstream ss;
    ss << "{\"node_id\":" << parent_id
       << ",\"kind\":\"refine\",\"rule\":\"expose_at_clause\""
       << ",\"formula\":" << formula_to_json(snapshot)
       << ",\"variable\":" << var_id
       << ",\"clause\":" << target_pos
       << ",\"children_ids\":";
    write_ids(ss, children_ids);
    ss << "}\n";
    out << ss.str();
}

void CertLogger::log_divide(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int target_idx, long long child_empty, long long child_not_empty)
{
    if (!out.is_open()) return;
    out << "{\"node_id\":" << parent_id
        << ",\"kind\":\"refine\",\"rule\":\"tail_empty_or_nonempty\""
        << ",\"formula\":" << formula_to_json(snapshot)
        << ",\"clause\":" << target_idx
        << ",\"children_ids\":[" << child_empty << ',' << child_not_empty
        << "]}\n";
}

std::string CertLogger::proof_node_to_json(const ProofNode &node)
{
    std::ostringstream ss;
    const std::string formula = formula_to_json(node.formula_snapshot);
    const bool is_call = node.type == "leaf" && node.vec.size() == 1 &&
                         node.vec[0] == 0 && node.tau >= 99.0;

    if (is_call)
    {
        ss << "{\"kind\":\"call\",\"formula\":" << formula << '}';
        return ss.str();
    }

    if (node.type == "leaf" && !node.rule.empty())
    {
        if (!MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
            throw std::logic_error(
                "strict proof mode reached a named assumption: " + node.rule);
        ss << "{\"kind\":\"assumption\",\"formula\":" << formula
           << ",\"name\":\"" << node.rule << "\",\"vector\":[";
        for (size_t i = 0; i < node.vec.size(); ++i)
        {
            if (i) ss << ',';
            ss << node.vec[i];
        }
        ss << "]}";
        return ss.str();
    }

    if (node.type == "enumeration" && !node.alternatives.empty())
    {
        ss << "{\"kind\":\"decompose\",\"transition\":\"semantic\""
           << ",\"formula\":" << formula << ",\"alternatives\":[";
        for (size_t i = 0; i < node.alternatives.size(); ++i)
        {
            if (i) ss << ',';
            const ProofAlternative &alternative = node.alternatives[i];
            ss << "{\"offset\":" << alternative.offset
               << ",\"decrease\":" << alternative.decrease
               << ",\"formula\":"
               << formula_to_json(alternative.proof->formula_snapshot)
               << ",\"proof\":" << proof_node_to_json(*alternative.proof) << '}';
        }
        ss << "]}";
        return ss.str();
    }

    if (node.type == "branch" && node.children.size() == 2)
    {
        ss << "{\"kind\":\"decompose\",\"transition\":\"assign\""
           << ",\"formula\":" << formula
           << ",\"variable\":" << node.pivot_id
           << ",\"alternatives\":["
           << "{\"offset\":" << node.offset_true
           << ",\"decrease\":" << node.reduced_cnt_true
           << ",\"formula\":" << formula_to_json(node.children[0].formula_snapshot)
           << ",\"proof\":" << proof_node_to_json(node.children[0]) << "},"
           << "{\"offset\":" << node.offset_false
           << ",\"decrease\":" << node.reduced_cnt_false
           << ",\"formula\":" << formula_to_json(node.children[1].formula_snapshot)
           << ",\"proof\":" << proof_node_to_json(node.children[1]) << "}] }";
        return ss.str();
    }

    if (node.type == "reduction" && node.children.size() == 1)
    {
        int reward = (int)node.formula_snapshot.size() -
                     (int)node.children[0].formula_snapshot.size();
        ss << "{\"kind\":\"decompose\",\"transition\":\"semantic\""
           << ",\"formula\":" << formula
           << ",\"alternatives\":[{\"offset\":\"infer\""
           << ",\"decrease\":" << reward
           << ",\"formula\":" << formula_to_json(node.children[0].formula_snapshot)
           << ",\"proof\":" << proof_node_to_json(node.children[0]) << "}]"
           << ",\"explanation\":{\"rule\":\"" << node.rule
           << "\",\"pivot\":" << node.pivot_id << "}}";
        return ss.str();
    }

    if (node.type == "divide_clause" && node.children.size() == 2)
    {
        ss << "{\"kind\":\"refine\",\"rule\":\"tail_empty_or_nonempty\""
           << ",\"formula\":" << formula
           << ",\"clause\":" << node.target_clause_idx
           << ",\"children\":[" << proof_node_to_json(node.children[0])
           << ',' << proof_node_to_json(node.children[1]) << "]}";
        return ss.str();
    }

    // A legacy vector is deliberately not treated as a proof.  It is emitted
    // as an incomplete decomposition so that the small verifier reports the
    // first place where constructive child formulas are still missing.
    ss << "{\"kind\":\"decompose\",\"transition\":\"legacy_claim\""
       << ",\"formula\":" << formula << ",\"alternatives\":[]"
       << ",\"legacy_vector\":[";
    for (size_t i = 0; i < node.vec.size(); ++i)
    {
        if (i) ss << ',';
        ss << node.vec[i];
    }
    ss << "]}";
    return ss.str();
}

void CertLogger::log_proof_tree(long long parent_id,
                                const ProofNode &root_node)
{
    if (!out.is_open()) return;
    out << "{\"node_id\":" << parent_id
        << ",\"kind\":\"strategy\",\"formula\":"
        << formula_to_json(root_node.formula_snapshot)
        << ",\"proof\":"
        << proof_node_to_json(root_node) << "}\n";
}
