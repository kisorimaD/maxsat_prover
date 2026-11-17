#include "cert_logger.h"
#include "lemmas.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <iomanip>

CertLogger global_logger;
std::ofstream out;

void CertLogger::init(const std::string &filename)
{
    out.open(filename, std::ios::out | std::ios::trunc);
    if (!out.is_open())
        throw std::runtime_error("Cannot open certificate log: " + filename);
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
std::string json_string(const std::string &value)
{
    std::ostringstream ss;
    ss << '"';
    for (unsigned char ch : value)
    {
        if (ch == '"' || ch == '\\') ss << '\\' << ch;
        else if (ch < 32) ss << "\\u" << std::hex << std::setw(4) << std::setfill('0') << int(ch) << std::dec;
        else ss << ch;
    }
    ss << '"';
    return ss.str();
}

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

void write_exclusions(std::ostream &ss, const TailExclusions &exclusions)
{
    if (exclusions.empty()) return;
    ss << ",\"tail_exclusions\":[";
    bool first = true;
    for (const auto &[tail, types] : exclusions)
    {
        if (!first) ss << ',';
        first = false;
        ss << "{\"tail\":" << tail << ",\"types\":[";
        bool first_type = true;
        for (const auto &d : types) {
            if (!first_type) ss << ',';
            first_type = false;
            ss << '[' << d[0] << ',' << d[1] << ',' << (d[2] ? "true" : "false") << ']';
        }
        ss << "]}";
    }
    ss << ']';
}
}

void CertLogger::log_add_variable(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int var_id, int pos_deg, int neg_deg, LitType type,
    const std::vector<long long> &children_ids)
{
    if (!out.is_open()) return;
    if (!snapshot.empty())
        throw std::logic_error("add declares the root family only; use addpos for refinements");
    std::ostringstream ss;
    ss << "{\"node_id\":" << parent_id
       << ",\"kind\":\"root_family\""
       << ",\"formula\":" << formula_to_json(snapshot)
       << ",\"variable\":" << var_id
       << ",\"positive\":" << pos_deg
       << ",\"negative\":" << neg_deg
       << ",\"singleton\":" << (type == SINGLETON ? "true" : "false")
       << ",\"children_ids\":";
    write_ids(ss, children_ids);
    if (lemma_export_enabled())
        ss << ",\"lemma_export\":{\"q\":" << json_string(lemma_export_settings.target)
           << ",\"output\":" << json_string(lemma_export_settings.output_file) << '}';
    if (!saved_lemma_sources().empty())
    {
        ss << ",\"lemma_sources\":[";
        bool first = true;
        for (const auto &source : saved_lemma_sources())
        {
            if (!first) ss << ',';
            first = false;
            ss << "{\"id\":" << json_string(source.id) << ",\"digest\":" << json_string(source.digest)
               << ",\"path\":" << json_string(source.path) << '}';
        }
        ss << ']';
    }
    ss << "}\n";
    out << ss.str();
}

void CertLogger::log_addpos(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int var_id, int target_pos, const std::vector<LiteralDegType> &degrees,
    const std::vector<long long> &children_ids, const TailExclusions &exclusions)
{
    if (!out.is_open()) return;
    std::ostringstream ss;
    ss << "{\"node_id\":" << parent_id
       << ",\"kind\":\"refine\",\"rule\":\"expose_at_clause\""
       << ",\"formula\":" << formula_to_json(snapshot)
       << ",\"variable\":" << var_id
       << ",\"clause\":" << target_pos << ",\"degrees\":[";
    for (size_t i = 0; i < degrees.size(); ++i)
    {
        if (i) ss << ',';
        ss << '[' << degrees[i].i << ',' << degrees[i].j << ','
           << (degrees[i].type == SINGLETON ? "true" : "false") << ']';
    }
    ss << "],\"children_ids\":";
    write_ids(ss, children_ids);
    write_exclusions(ss, exclusions);
    ss << "}\n";
    out << ss.str();
}

void CertLogger::log_expose_type(const CNF &parent, int variable, int clause,
    LiteralDegType degree, const vector<LiteralDegType> &scope,
    const vector<long long> &children)
{
    if (!out.is_open()) return;
    std::ostringstream ss;
    ss << "{\"node_id\":" << parent.node_id
       << ",\"kind\":\"refine\",\"rule\":\"expose_type_at_clause\",\"formula\":"
       << formula_to_json(parent.get_cert_snapshot()) << ",\"variable\":" << variable
       << ",\"clause\":" << clause << ",\"degree\":[" << degree.i << ',' << degree.j
       << ',' << (degree.type == SINGLETON ? "true" : "false") << "],\"degrees\":[";
    for (size_t i = 0; i < scope.size(); ++i) {
        if (i) ss << ',';
        ss << '[' << scope[i].i << ',' << scope[i].j << ','
           << (scope[i].type == SINGLETON ? "true" : "false") << ']';
    }
    ss << "],\"children_ids\":";
    write_ids(ss, children);
    write_exclusions(ss, parent.active_tail_exclusions());
    ss << "}\n";
    out << ss.str();
}

void CertLogger::log_divide(
    long long parent_id, const std::vector<std::vector<int>> &snapshot,
    int target_idx, long long child_empty, long long child_not_empty,
    const TailExclusions &exclusions)
{
    if (!out.is_open()) return;
    out << "{\"node_id\":" << parent_id
        << ",\"kind\":\"refine\",\"rule\":\"tail_empty_or_nonempty\""
        << ",\"formula\":" << formula_to_json(snapshot)
        << ",\"clause\":" << target_idx
        << ",\"children_ids\":[" << child_empty << ',' << child_not_empty << ']';
    write_exclusions(out, exclusions);
    out << "}\n";
}

std::string CertLogger::proof_node_to_json(const ProofNode &node)
{
    std::ostringstream ss;
    const std::string formula = formula_to_json(node.formula_snapshot);
    const bool is_call = node.type == "leaf" && node.vec.size() == 1 &&
                         node.vec[0] == 0 && node.tau >= 99.0;

    if (node.type=="restart" && node.children.size()==1) {
        ss << "{\"kind\":\"restart\",\"formula\":" << formula
           << ",\"variable\":" << node.pivot_id << ",\"rule\":\"" << node.rule
           << "\",\"proof\":{\"kind\":\"call\",\"formula\":"
           << formula_to_json(node.children[0].formula_snapshot) << "}}";
        return ss.str();
    }
    if (is_call)
    {
        ss << "{\"kind\":\"call\",\"formula\":" << formula << '}';
        return ss.str();
    }

    if (node.type == "lemma")
    {
        if (!node.lemma_application)
            throw std::logic_error("lemma leaf has no application witness");
        const LemmaApplication &application = *node.lemma_application;
        ss << "{\"kind\":\"lemma\",\"formula\":" << formula
           << ",\"name\":" << json_string(application.id) << ",\"roles\":";
        auto write_values = [&](const std::vector<int> &values) {
            ss << '[';
            for (size_t i = 0; i < values.size(); ++i)
            {
                if (i) ss << ',';
                ss << values[i];
            }
            ss << ']';
        };
        write_values(application.role_literals);
        ss << ",\"witness_clauses\":";
        write_values(application.witness_clauses);
        ss << ",\"vector\":";
        write_values(application.vector);
        if (!application.definition_digest.empty())
            ss << ",\"definition_digest\":" << json_string(application.definition_digest);
        if (!application.degree_scope.empty())
        {
            ss << ",\"degree_scope\":[";
            for (size_t i = 0; i < application.degree_scope.size(); ++i)
            {
                if (i) ss << ',';
                const auto &degree = application.degree_scope[i];
                ss << '[' << degree[0] << ',' << degree[1] << ',' << (degree[2] ? "true" : "false") << ']';
            }
            ss << ']';
        }
        ss << '}';
        return ss.str();
    }

    if (node.type == "lemma3_split")
    {
        if (!MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS || node.children.size() != 1)
            throw std::logic_error("invalid imported lemma3 split");
        ss << "{\"kind\":\"lemma3_split\",\"formula\":" << formula
           << ",\"variable\":" << node.pivot_id
           << ",\"long_decrease\":" << node.lemma3_long_decrease
           << ",\"proof\":" << proof_node_to_json(node.children[0]) << '}';
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

    if (node.type == "xiao_property1_branch")
    {
        if (!MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS || node.children.size() != 2 ||
            node.property1_sides.size() != 2 || node.property2_sides.size() != 2 ||
            node.property1_scope.empty()) throw std::logic_error("invalid imported Property 1 branch");
        ss << "{\"kind\":\"xiao_property1_branch\",\"formula\":" << formula
           << ",\"variable\":" << node.pivot_id << ",\"properties\":[";
        for (int side = 0; side < 2; ++side)
            ss << (side ? "," : "") << (node.property1_sides[side] ? 1 : node.property2_sides[side] ? 2 : 0);
        ss << "],\"degrees\":[";
        for (size_t i = 0; i < node.property1_scope.size(); ++i) {
            const auto &d = node.property1_scope[i];
            ss << (i ? "," : "") << '[' << d[0] << ',' << d[1] << ',' << (d[2] ? "true" : "false") << ']';
        }
        ss << "],\"children\":[" << proof_node_to_json(node.children[0])
           << ',' << proof_node_to_json(node.children[1]) << "]}";
        return ss.str();
    }

    if (node.type == "xiao_property2_branch")
    {
        if (!MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS || node.children.size() != 2 ||
            node.property2_sides.size() != 2)
            throw std::logic_error("invalid imported Property 2 branch");
        ss << "{\"kind\":\"xiao_property2_branch\",\"formula\":" << formula
           << ",\"variable\":" << node.pivot_id
           << ",\"imported_sides\":[" << (node.property2_sides[0] ? "true" : "false")
           << ',' << (node.property2_sides[1] ? "true" : "false") << ']'
           << ",\"children\":[" << proof_node_to_json(node.children[0])
           << ',' << proof_node_to_json(node.children[1]) << "]}";
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
        if (node.rule == "RR10" || node.rule == "RR11")
        {
            ss << "{\"kind\":\"local_resolution\",\"formula\":" << formula
               << ",\"variable\":" << node.pivot_id << ",\"rule\":\"" << node.rule
               << "\",\"proof\":" << proof_node_to_json(node.children[0]) << '}';
            return ss.str();
        }
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
                                const ProofNode &root_node, const TailExclusions &exclusions)
{
    if (!out.is_open()) return;
    out << "{\"node_id\":" << parent_id
        << ",\"kind\":\"strategy\",\"formula\":"
        << formula_to_json(root_node.formula_snapshot)
        << ",\"proof\":"
        << proof_node_to_json(root_node);
    write_exclusions(out, exclusions);
    out << "}\n";
}

std::string CertLogger::serialize_proof(const ProofNode &root_node)
{
    return proof_node_to_json(root_node);
}

std::string CertLogger::serialize_state(const CNF &formula)
{
    std::ostringstream ss;
    ss << "{\"formula\":" << formula_to_json(formula.get_cert_snapshot());
    write_exclusions(ss, formula.active_tail_exclusions());
    ss << '}';
    return ss.str();
}

void CertLogger::log_rollback(const std::vector<long long> &parents)
{
    if (!out.is_open() || parents.empty()) return;
    std::ostringstream ss;
    ss << "{\"kind\":\"rollback\",\"parent_ids\":";
    write_ids(ss,parents);ss << "}\n";out << ss.str();
}
