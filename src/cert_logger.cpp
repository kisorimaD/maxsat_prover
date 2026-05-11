#include "cert_logger.h"
#include "cnf.h"

TreeLogger global_logger("proof_tree.json", 1.2872);

TreeLogger::TreeLogger(const std::string& filename, double target_bound) {
    out.open(filename);
    indent_level = 0;
    needs_comma = false;
    out << "{\n  \"universe\": {\"target_bound\": " << target_bound << "},\n  \"proof_tree\": [\n";
}

TreeLogger::~TreeLogger() {
    out << "\n  ]\n}\n";
    out.close();
}

void TreeLogger::print_indent() {
    for(int i = 0; i < indent_level; ++i) out << "  ";
}   

void TreeLogger::write_formula(CNF* cnf) {
    out << "[";
    for (size_t i = 0; i < cnf->clauses.size(); ++i) {
        if (i > 0) out << ", ";
        out << "[";
        // for (size_t j = 0; j < cnf->clauses[i]->lits.size(); ++j) {
        bool first_flag = true;
        for(Literal* lit : cnf->clauses[i]->lits)
        {
            if (!first_flag) 
                out << ", ";
            else
                first_flag = false;
            
            int lit_id = lit->id;
            bool inv = lit->inv;
            if (lit_id == 0 || lit_id == 1) {
                out << lit_id; // Вывод маркеров 0 и 1 без инверсии
            } else {
                out << (inv? "-" : "") << lit_id;
            }
        }
        out << "]";
    }
    out << "]";
}

TreeLogger::NodeScope TreeLogger::open_node() {
    if (needs_comma) out << ",\n";
    print_indent();
    out << "{\n";
    indent_level++;
    needs_comma = false;
    return NodeScope(*this);
}

void TreeLogger::close_node() {
    indent_level--;
    out << "\n";
    print_indent();
    out << "}";
    needs_comma = true;
}

// Замените старый begin_children на этот (добавлена открывающая скобка массива):
void TreeLogger::begin_children() {
    if (needs_comma) out << ",\n";
    print_indent(); out << "\"children\": [\n";
    needs_comma = false;
}

void TreeLogger::end_children() {
    out << "\n";
    print_indent(); out << "]";
    needs_comma = true;
}

void TreeLogger::log_divide(const std::string& id, int clause_idx, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"divide_clause\",\n";
    print_indent(); out << "\"target_clause_idx\": " << clause_idx << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}

void TreeLogger::log_reduction(const std::string& id, const std::string& rule, int pivot, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"reduction\",\n";
    print_indent(); out << "\"rule\": \"" << rule << "\",\n";
    print_indent(); out << "\"pivot_id\": " << pivot << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}

void TreeLogger::log_branch(const std::string& id, int pivot, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"branch\",\n";
    print_indent(); out << "\"branching_variable\": " << pivot << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}

void TreeLogger::log_add_var(const std::string& id, const std::string& var, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"add_variable\",\n";
    print_indent(); out << "\"added_variable\": \"" << var << "\",\n";
    print_indent(); out << "\"formula\": "; write_formula(cnf); out << "\n";
    needs_comma = true;
}

void TreeLogger::log_leaf(const std::string& id, const std::vector<int>& vec, double tau, CNF* cnf, const std::vector<int>& partition) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"leaf\",\n";
    print_indent(); out << "\"vector\": [";
    for(size_t i=0; i<vec.size(); ++i) { if(i>0) out<<","; out<<vec[i]; }
    out << "],\n";
    print_indent(); out << "\"partition\": [";
    for(size_t i=0; i<partition.size(); ++i) { if(i>0) out<<","; out<<partition[i]; }
    out << "],\n";
    print_indent(); out << "\"tau\": " << tau << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}