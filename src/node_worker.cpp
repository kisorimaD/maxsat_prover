#include "node_worker.h"
#include "cnf.h"
#include "cert_logger.h"
#include "lemmas.h"
#include <algorithm>
#include <cmath>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>

namespace {
template<class T> T read() { T value; if (!(std::cin >> value)) throw std::invalid_argument("incomplete node request"); return value; }
bool flag() { int v=read<int>(); if (v!=0 && v!=1) throw std::invalid_argument("invalid boolean"); return v; }
LiteralDegType degree() {
    int p=read<int>(),n=read<int>(); bool s=flag();
    validate_degree(p,n,s?SINGLETON:ANY); return {p,n,s?SINGLETON:ANY};
}
}

int run_node_worker(const std::vector<std::string> &lemma_files)
{
    try {
        if (read<std::string>()!="MAXSAT_NODE_V1") throw std::invalid_argument("unsupported node protocol");
        const std::string operation=read<std::string>(),q_text=read<std::string>();
        size_t consumed=0; double q=std::stod(q_text,&consumed);
        if (consumed!=q_text.size() || !std::isfinite(q) || q<=1) throw std::invalid_argument("invalid q");
        bool imports=flag(),p1=flag(),p2=flag(),restarts=flag();
        int depth=read<int>(),groups=read<int>(),child_limit=read<int>(),max_variables=read<int>(),max_clauses=read<int>();
        if (depth<0 || depth>30 || groups<0 || groups>MAX_MASK_BITS || child_limit<1 ||
            max_variables<1 || max_variables>MAX_MASK_BITS || max_clauses<1 || max_clauses>MAX_MASK_BITS)
            throw std::invalid_argument("invalid node limits");
        // preprocess historically prints diagnostics. Keep the machine channel clean.
        std::ostringstream diagnostics;
        auto *previous=std::cout.rdbuf(diagnostics.rdbuf());
        try { preprocess(); } catch (...) { std::cout.rdbuf(previous); throw; }
        std::cout.rdbuf(previous);
        MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS=imports;
        MaxSATSettings.ALLOW_XIAO_PROPERTY1=p1;
        MaxSATSettings.ALLOW_XIAO_PROPERTY2=p2;
        MaxSATSettings.ALLOW_POLYNOMIAL_RESTARTS=restarts;
        set_lemma_search_target(q_text);
        int family_count=read<int>();
        if (family_count<1 || family_count>128) throw std::invalid_argument("invalid degree family size");
        std::vector<LiteralDegType> scope;
        for (int i=0;i<family_count;++i) scope.push_back(degree());
        set_lemma_degree_scope(scope);
        load_saved_lemmas(lemma_files);
        std::unique_ptr<CNF,decltype(&destroy_cnf)> formula(new CNF(),destroy_cnf);
        int count=read<int>();
        if (count<1 || count>max_clauses) throw std::invalid_argument("invalid clause count");
        std::set<int> ids,tails;
        for (int i=0;i<count;++i) {
            int size=read<int>(); if (size<1 || size>4096) throw std::invalid_argument("invalid clause size");
            std::vector<Literal*> literals; std::map<int,bool> atoms; std::set<int> seen;
            for (int j=0;j<size;++j) {
                int value=read<int>();
                if (!seen.insert(value).second) throw std::invalid_argument("duplicate literal");
                if (value>=SNAP_TAIL_ANY_BASE) {
                    bool nonempty=value>=SNAP_TAIL_NONEMPTY_BASE;
                    int tail=value-(nonempty?SNAP_TAIL_NONEMPTY_BASE:SNAP_TAIL_ANY_BASE);
                    if (tail<0 || tail>1000000 || !tails.insert(tail).second || !atoms.empty())
                        throw std::invalid_argument("node protocol needs independent single tails");
                    atoms[tail]=nonempty; reserve_tail_atoms(tail);
                    literals.push_back(nonempty?&UNKNOWN_NOT_EMPTY_LITERAL:&UNKNOWN_LITERAL);
                } else {
                    if (value==0 || value==1 || value==-1 || value<=-SNAP_TAIL_ANY_BASE)
                        throw std::invalid_argument("invalid ordinary literal");
                    int id=std::abs(value);ids.insert(id);ID_COUNTER=std::max(ID_COUNTER,id+1);
                    std::string name="v"+std::to_string(id);VAR2ID[name]=id;ID2VAR[id]=name;
                    literals.push_back(intern_literal(id,value<0));
                }
            }
            if (std::none_of(literals.begin(),literals.end(),[](auto *l){return !is_any_unknown_literal(l);}))
                throw std::invalid_argument("node clauses need an ordinary literal");
            formula->clauses.push_back(new Clause(literals,atoms));
        }
        if (ids.size()>size_t(max_variables)) throw std::invalid_argument("node exceeds variable bound");
        int exclusions=read<int>();
        if (exclusions<0 || exclusions>count) throw std::invalid_argument("invalid exclusion count");
        for (int i=0;i<exclusions;++i) {
            int tail=read<int>(),types=read<int>();
            if (!tails.count(tail) || formula->tail_exclusions.count(tail) || types<1 || types>128)
                throw std::invalid_argument("invalid tail exclusions");
            for (int j=0;j<types;++j) {
                auto d=degree();
                if (!formula->tail_exclusions[tail].insert({d.i,d.j,d.type==SINGLETON}).second)
                    throw std::invalid_argument("duplicate excluded type");
            }
        }
        int index=read<int>();
        LiteralDegType requested{0,0,ANY};
        if (operation=="TYPE") requested=degree();
        std::string extra;if (std::cin>>extra) throw std::invalid_argument("trailing node request data");
        if (operation=="CHECK") {
            ProofNode best=formula->branch(std::vector<int>(ids.begin(),ids.end()));
            auto consider=[&](ProofNode p) {
                if (branching_weight(p.vec,q)<branching_weight(best.vec,q) ||
                    (meets_strategy_target(p,q) && !meets_strategy_target(best,q))) best=std::move(p);
            };
            for (int d=0;d<=depth && !meets_strategy_target(best,q);++d) {
                consider(formula->xiao_branch(d,"",q));
            }
            if (!meets_strategy_target(best,q) && ids.size()<=size_t(groups)) {
                consider(formula->branch_group(std::vector<int>(ids.begin(),ids.end()),-1,true,q));
            }
            std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"checked\",\"proof\":"
                      << global_logger.serialize_proof(best) << "}\n";
            return 0;
        }
        if (index<0 || index>=count || formula->clauses[index]->tail_atoms.size()!=1)
            throw std::invalid_argument("invalid target clause");
        std::vector<CNF*> children;
        if (operation=="EXPOSE" || operation=="TYPE") {
            if (ids.size()>=size_t(max_variables)) {
                std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"skipped\",\"reason\":\"variable bound\"}\n";return 0;
            }
            std::string name="witness";
            if (VAR2ID.count(name)) throw std::logic_error("reserved witness name");
            size_t reserved=operation=="TYPE" || formula->clauses[index]->lits.count(&UNKNOWN_LITERAL) ? 1 : 0;
            set_exposure_child_limit(size_t(child_limit)-reserved);
            try {
                children=operation=="TYPE"
                    ? expose_type_in_place(formula.get(),name,[index](CNF*){return index;},requested,scope)
                    : add_new_var_in_place(formula.get(),name,[index](CNF*){return index;},scope);
            } catch (const ExposureLimitExceeded &) {
                std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"skipped\",\"reason\":\"children bound\"}\n";return 0;
            }
        } else if (operation=="SPLIT") {
            if (formula->clauses[index]->tail_atoms.begin()->second)
                throw std::invalid_argument("split requires an unrestricted tail");
            auto *empty=new CNF(*formula),*nonempty=new CNF(*formula);
            empty->clauses[index]->lits.erase(&UNKNOWN_LITERAL);empty->clauses[index]->tail_atoms.clear();
            auto *clause=nonempty->clauses[index];clause->lits.erase(&UNKNOWN_LITERAL);
            clause->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);clause->tail_atoms.begin()->second=true;
            children={empty,nonempty};
        } else throw std::invalid_argument("unknown node operation");
        std::vector<std::unique_ptr<CNF,decltype(&destroy_cnf)>> owners;
        for (auto *child:children) if (child!=formula.get()) owners.emplace_back(child,destroy_cnf);
        bool too_large=children.size()>size_t(child_limit);
        for (auto *child:children) too_large|=child->clauses.size()>size_t(max_clauses);
        if (children.empty()) {
            std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"skipped\",\"reason\":\"empty expansion needs an explicit contradiction proof\"}\n";return 0;
        }
        if (too_large) {
            std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"skipped\",\"reason\":\"children or clause bound\"}\n";return 0;
        }
        std::cout << "{\"format\":\"maxsat-node-result-v1\",\"status\":\"expanded\",\"children\":[";
        for (size_t i=0;i<children.size();++i)
            std::cout << (i?",":"") << global_logger.serialize_state(*children[i]);
        std::cout << "]}\n";return 0;
    } catch (const std::exception &e) {
        std::cerr << "node-worker: " << e.what() << '\n';return 1;
    }
}
