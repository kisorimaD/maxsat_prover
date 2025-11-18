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

struct{
    int MAXIMUM_CLAUSE_SIZE;
} MaxSATSettings;

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

struct LiteralDegType{
    int i;
    int j;
    LitType type;
};

extern vector <LiteralDegType> POSSIBLE_LITERALS; 

struct RRuleInfo
{
    int clauses_reduced;
    string message;
};

class CNF
{

public:
    CNF() {}
    CNF(vector<Clause *> clauses) : clauses(clauses) {}
    CNF(CNF &cnf)
    {
        clauses.resize(cnf.clauses.size());
        for (int i = 0; i < (int)clauses.size(); ++i)
        {
            clauses[i] = new Clause(*cnf.clauses[i]);
        }
    }

    vector<int> branch(vector<int> ids);

    vector<int> branch_group(vector<int> ids, int max_partitions = -1);

    vector<Clause *> clauses;
};

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type); //,const std::function<bool(int, bool, bool, Clause*)>& condition_func = [](int, bool, bool, Clause*){ return true; });
vector<CNF *> add_new_var_in_place(CNF *cnf, string v_name, const std::function<int(CNF *)> &need_index_func, vector <LiteralDegType> variants = POSSIBLE_LITERALS);


bool is_A_subset_of_B(int A, int B);
double branching_factor(const vector<int> &a, double tol = 1e-12);

void print_clause(Clause &c);
void print_cnf(CNF &cnf);

void preprocess(int maximum_clause_size = -1);