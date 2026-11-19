#pragma once

#include <string>
#include <map>
#include <vector>
#include <set>
#include <functional>
#include <memory>

using namespace std;

// Signed int masks deliberately leave the sign bit unused.
constexpr int MAX_MASK_BITS = 30;

extern map<int, string> ID2VAR;
extern map<string, int> VAR2ID;
extern int ID_COUNTER;

double branching_factor(const vector<int> &a, double tol = 1e-12);
long double branching_weight(const vector<int> &a, double q);
vector<int> reduction_or_branch_bound(const vector<int> &branch_vector, double q);
bool meets_branching_target(const vector<int> &a, double q);

struct MaxSATSettingsType
{
    // Strict proof-search mode.  When false, heuristic leaves whose only
    // justification is a named paper lemma are not considered at all.
    bool ALLOW_NAMED_ASSUMPTIONS;
};

extern MaxSATSettingsType MaxSATSettings;

struct ProofAlternative;

struct ProofNode {
    std::string type;       // "leaf", "reduction", "branch"
    std::string rule;       // Название правила (например, "RR3")
    int pivot_id = -1;      // Переменная, по которой идет ветвление/редукция
    std::vector<int> vec;   // Итоговый вектор редукций (например, {3, 3})
    double tau = 100.0;     // Итоговый branching factor
    // Imported branching case serialized independently of the bound at q.
    std::vector<int> assumption_branch_vector;
   
    std::vector<std::vector<int>> cover_groups; // grouped branching may overlap
    std::vector<std::vector<int>> formula_snapshot; 
    
    std::vector<ProofNode> children;
    // Constructive alternatives used by plain and grouped branching.  The
    // old `vec` remains a search heuristic only; the certificate logger emits
    // these alternatives instead of trusting it.
    std::vector<ProofAlternative> alternatives;

    std::map<int, int> subsumptions; 
    
    int reduced_cnt_true = 0;
    int reduced_cnt_false = 0;
    int offset_true = 0;
    int offset_false = 0;

    ProofNode() {}
    
    ProofNode(std::vector<int> v) : type("leaf"), vec(v), tau(branching_factor(v)) {}
};

struct ProofAlternative {
    int offset = 0;          // clauses certainly satisfied in this alternative
    int decrease = 0;        // clauses removed from the global m-parameter
    std::vector<int> represented_masks;
    std::shared_ptr<ProofNode> proof;
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

int fresh_tail_atom();

// Snapshot-only encoding.  Ordinary literals never approach these values.
constexpr int SNAP_TAIL_ANY_BASE = 1000000000;
constexpr int SNAP_TAIL_NONEMPTY_BASE = 1500000000;

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
    Clause() : lits({&UNKNOWN_LITERAL}), empty(true)
    {
        tail_atoms[fresh_tail_atom()] = false;
    }
    Clause(const vector<Literal *> &lits_vec) : empty(lits_vec.size() == 1 && lits_vec[0] == &UNKNOWN_LITERAL)
    {
        for (auto lit : lits_vec)
            lits.insert(lit);
        bool any = false;
        bool nonempty = false;
        for (auto lit : lits_vec)
        {
            any |= lit == &UNKNOWN_LITERAL;
            nonempty |= lit == &UNKNOWN_NOT_EMPTY_LITERAL;
        }
        if (any || nonempty) tail_atoms[fresh_tail_atom()] = nonempty;
    }
    Clause(const vector<Literal *> &lits_vec, const map<int, bool> &tails)
        : Clause(lits_vec) { tail_atoms = tails; }
    Clause(const set<Literal *, LiteralPtrLess> &lits) : lits(lits), empty(lits.size() == 1 && *lits.begin() == &UNKNOWN_LITERAL)
    {
        bool any = lits.count(&UNKNOWN_LITERAL);
        bool nonempty = lits.count(&UNKNOWN_NOT_EMPTY_LITERAL);
        if (any || nonempty) tail_atoms[fresh_tail_atom()] = nonempty;
    }
    Clause(const Clause &c) : lits(c.lits), empty(c.empty), tail_atoms(c.tail_atoms) {}

    set<Literal *, LiteralPtrLess> lits;
    bool empty;
    // Each entry is an independent boundary disjunction; the bool records
    // that its underlying list is known nonempty.  Multiple entries mean OR.
    map<int, bool> tail_atoms;
};

enum LitType
{
    SINGLETON,
    NON_SINGLETON,
    ANY
};

void validate_degree(int positive, int negative, LitType type);

struct LiteralDegType
{
    int i;
    int j;
    LitType type;
};

extern vector<LiteralDegType> POSSIBLE_LITERALS;

struct FormulaVarStats
{
    int pos_count = 0;
    int neg_count = 0;
    int pos_unit_count = 0;
    int neg_unit_count = 0;
    int pos_min_D = 999999;
    int neg_min_D = 999999;
    vector<int> pos_indices;
    vector<int> neg_indices;
};

class CNF
{

public:
    CNF();

    CNF(CNF &cnf);

    ProofNode branch(vector<int> ids);

    ProofNode branch_group(vector<int> ids, bool construct_proof = false,
                           double q = 1.2873);


    std::vector<std::vector<int>> get_snapshot();
    std::vector<std::vector<int>> get_cert_snapshot() const;

    long long node_id;

    vector<Clause *> clauses;

private:
};

struct GroupResidual
{
    CNF *cnf = nullptr;
    int base_decrease = 0;
    int common_satisfied_mask = 0;
    int common_empty_mask = 0;
    map<int, pair<int, bool>> representative_map;
    bool valid = false;
    string error;
};

struct ReductionStep
{
    bool applied = false;
    string rule;
    int pivot_id = -1;
    int decrease = 0;
    vector<int> witness_clauses;
    CNF *cnf = nullptr;
    vector<vector<int>> formula_snapshot;
};

struct ReductionFixpoint
{
    CNF *cnf = nullptr;
    int total_decrease = 0;
    vector<ReductionStep> steps;
};

bool is_any_unknown_literal(const Literal *l);
map<int, FormulaVarStats> analyze_formula(const CNF &cnf);
GroupResidual materialize_group_residual(const CNF &cnf,
                                         const vector<int> &ids,
                                         const vector<int> &group_masks);
void destroy_cnf(CNF *cnf);
Literal *intern_literal(int id, bool inv);
ReductionStep apply_first_reduction(const CNF &cnf);
ReductionStep apply_named_reduction(const CNF &cnf, const string &rule);
ReductionFixpoint reduce_to_fixpoint(const CNF &cnf);

struct DivideResult {
    int clause_idx = -1;
    CNF* cnf_empty = nullptr;
    CNF* cnf_not_empty = nullptr;
};


vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type);
vector<CNF *> add_new_var_in_place(CNF *cnf, string v_name, const std::function<int(CNF *)> &need_index_func, vector<LiteralDegType> variants = POSSIBLE_LITERALS);

DivideResult empty_divide(CNF* cnf, double q = 1.2873);

bool is_A_subset_of_B(int A, int B);
bool check_group_validity(const vector<int>& group_masks, int k, string& diag);



void print_clause(Clause &c);
void print_cnf(CNF &cnf);

void preprocess();
