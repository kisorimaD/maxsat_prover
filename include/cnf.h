#pragma once

#include <string>
#include <map>
#include <vector>
#include <set>
#include <functional>

using namespace std;

extern map<int, string> ID2VAR;
extern map<string, int> VAR2ID;
extern int ID_COUNTER;

extern double C; // Временная константа, решения ниже которой мы отбрасываем

double branching_factor(const vector<int> &a, double tol = 1e-12);

struct
{
    int MAXIMUM_CLAUSE_SIZE;
} MaxSATSettings;

struct ProofNode {
    std::string type;       // "leaf", "reduction", "branch"
    std::string rule;       // Название правила (например, "RR3")
    int pivot_id = -1;      // Переменная, по которой идет ветвление/редукция
    std::vector<int> vec;   // Итоговый вектор редукций (например, {3, 3})
    double tau = 100.0;     // Итоговый branching factor
   
    int target_clause_idx = -1; // Для узла empty_divide
    std::vector<int> partition;
    std::vector<std::vector<int>> formula_snapshot; 
    
    std::vector<ProofNode> children;

    ProofNode() {}
    
    ProofNode(std::vector<int> v) : type("leaf"), vec(v), tau(branching_factor(v)) {}
};


class Literal
{
public:
    Literal();
    Literal(string var, bool is_inv = false);
    Literal(int id, bool is_inv = false);
    Literal neg() const;

    int id;
    bool inv;
};

extern Literal UNKNOWN_LITERAL;
extern Literal UNKNOWN_NOT_EMPTY_LITERAL; // Новый литерал ?+

struct LiteralPtrLess
{
    bool operator()(const Literal *a, const Literal *b) const
    {
        if (a->id != b->id)
            return a->id < b->id;
        return a->inv < b->inv;
    }
};

class Clause
{
public:
    Clause() : lits({&UNKNOWN_LITERAL}), empty(true) {}
    Clause(const vector<Literal *> &lits_vec) : empty(lits_vec.size() == 1 && lits_vec[0] == &UNKNOWN_LITERAL)
    {
        for (auto lit : lits_vec)
            lits.insert(lit);
    }
    Clause(const set<Literal *, LiteralPtrLess> &lits) : lits(lits), empty(lits.size() == 1 && *lits.begin() == &UNKNOWN_LITERAL) {}
    Clause(const Clause &c) : lits(c.lits), empty(c.empty) {}

    set<Literal *, LiteralPtrLess> lits;
    bool empty;
};

enum LitType
{
    SINGLETON,
    NON_SINGLETON,
    ANY
};

struct LiteralDegType
{
    int i;
    int j;
    LitType type;
};

extern vector<LiteralDegType> POSSIBLE_LITERALS;

class CNF
{

public:
    CNF() {}

    CNF(CNF &cnf)
    {
        clauses.resize(cnf.clauses.size());
        for (int i = 0; i < (int)clauses.size(); ++i)
        {
            clauses[i] = new Clause(*cnf.clauses[i]);
        }
    }

    // ~CNF()
    // {
    //     for (auto c : clauses)
    //     {
    //         delete c;
    //     }
    // }

    ProofNode branch(vector<int> ids);

    ProofNode branch_group(vector<int> ids, int max_partitions = -1);

    ProofNode xiao_branch(int depth, string first_var = "x");

    std::vector<std::vector<int>> get_snapshot();

    vector<Clause *> clauses;


};

struct DivideResult {
    int clause_idx = -1;
    CNF* cnf_empty = nullptr;
    CNF* cnf_not_empty = nullptr;
    ProofNode proof_tree; // Общий предок, связывающий два поддерева
};


// int calculate_F(CNF &cnf, int var_id);

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type); //,const std::function<bool(int, bool, bool, Clause*)>& condition_func = [](int, bool, bool, Clause*){ return true; });
vector<CNF *> add_new_var_in_place(CNF *cnf, string v_name, const std::function<int(CNF *)> &need_index_func, vector<LiteralDegType> variants = POSSIBLE_LITERALS);

DivideResult empty_divide(CNF* cnf);

bool is_A_subset_of_B(int A, int B);

void print_clause(Clause &c);
void print_cnf(CNF &cnf);

void preprocess(int maximum_clause_size = -1);