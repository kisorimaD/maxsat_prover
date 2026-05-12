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

void TreeLogger::log_branch(const std::string& id, int pivot, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"branch\",\n";
    print_indent(); out << "\"branching_variable\": " << pivot << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}

void TreeLogger::log_add_var(const std::string& id, int var_id, int pos_deg, int neg_deg, CNF* cnf) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"add_variable\",\n";
    print_indent(); out << "\"added_variable_id\": " << var_id << ",\n";
    print_indent(); out << "\"pos_deg\": " << pos_deg << ",\n";
    print_indent(); out << "\"neg_deg\": " << neg_deg << ",\n";
    print_indent(); out << "\"formula\": "; write_formula(cnf); out << "\n";
    needs_comma = true;
}

void TreeLogger::log_reduction(const std::string& id, const std::string& rule, int pivot, CNF* cnf, const std::vector<int>& rr_witness_clauses) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"reduction\",\n";
    print_indent(); out << "\"rule\": \"" << rule << "\",\n";
    print_indent(); out << "\"pivot_id\": " << pivot << ",\n";
    
    if (!rr_witness_clauses.empty()) {
        print_indent(); out << "\"rr_witness_clauses\": [";
        for(size_t i=0; i<rr_witness_clauses.size(); ++i) { 
            if(i>0) out << ","; 
            out << rr_witness_clauses[i]; 
        }
        out << "],\n";
    }

    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}

void TreeLogger::log_leaf(const std::string& id, const std::vector<int>& vec, double tau, CNF* cnf, const std::vector<int>& partition, const std::map<int, int>& subsumptions, const std::vector<GroupWitness>& group_witnesses) {
    print_indent(); out << "\"node_id\": \"" << id << "\",\n";
    print_indent(); out << "\"type\": \"leaf\",\n";
    
    print_indent(); out << "\"vector\": [";
    for(size_t i=0; i<vec.size(); ++i) { if(i>0) out<<","; out<<vec[i]; }
    out << "],\n";
    
    print_indent(); out << "\"partition\": [";
    for(size_t i=0; i<partition.size(); ++i) { if(i>0) out<<","; out<<partition[i]; }
    out << "],\n";

    if (!subsumptions.empty()) {
        print_indent(); out << "\"subsumptions\": {\n";
        indent_level++;
        bool first = true;
        for (const auto& pair : subsumptions) {
            if (!first) out << ",\n";
            first = false;
            print_indent(); out << "\"" << pair.first << "\": " << pair.second;
        }
        out << "\n";
        indent_level--;
        print_indent(); out << "},\n";
    }

    if (!group_witnesses.empty()) {
        print_indent(); out << "\"group_witnesses\": [\n";
        indent_level++;
        for(size_t i=0; i<group_witnesses.size(); ++i) {
            if(i>0) out << ",\n";
            print_indent(); out << "{\n";
            indent_level++;
            
            print_indent(); out << "\"rule\": \"" << group_witnesses[i].rule << "\",\n";
            print_indent(); out << "\"basic_reduce_val\": " << group_witnesses[i].basic_reduce_val;
            
            if (group_witnesses[i].rule == "cross_reduce") {
                out << ",\n";
                print_indent(); out << "\"cross_row_idx\": " << group_witnesses[i].cross_row_idx << ",\n";
                print_indent(); out << "\"cross_size\": " << group_witnesses[i].cross_size;
            } else if (group_witnesses[i].rule == "lemma2" || group_witnesses[i].rule == "lemma3" || group_witnesses[i].rule == "double_lemma3") {
                out << ",\n";
                print_indent(); out << "\"lemma_var_id\": " << group_witnesses[i].lemma_var_id << ",\n";
                print_indent(); out << "\"lemma_local_D\": " << group_witnesses[i].lemma_local_D << ",\n";
                print_indent(); out << "\"lemma_pos_count\": " << group_witnesses[i].lemma_pos_count << ",\n";
                print_indent(); out << "\"lemma_neg_count\": " << group_witnesses[i].lemma_neg_count;
            }
            out << "\n";
            
            indent_level--;
            print_indent(); out << "}";
        }
        out << "\n";
        indent_level--;
        print_indent(); out << "],\n";
    }

    print_indent(); out << "\"tau\": " << tau << ",\n";
    print_indent(); out << "\"formula\": "; 
    if (cnf) write_formula(cnf); else out << "[]"; 
    out << "\n";
    needs_comma = true;
}