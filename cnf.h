#pragma once

#include <string>
#include <map>
#include <vector>
#include <set>

using namespace std;

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 1;

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

map<int, Literal *> ID2LIT;
Literal UNKNOWN_LITERAL = Literal();

struct LiteralPtrLess
{
    bool operator()(const Literal *a, const Literal *b) const
    {
        if (a->id != b->id)
            return a->id < b->id;
        return a->inv < b->inv;
    }
};

// Literal inv_literal(Literal &v);

class Clause
{
public:
    Clause() : lits({&UNKNOWN_LITERAL}) {}
    Clause(const vector<Literal *> &lits_vec)
    {
        for (auto lit : lits_vec)
            lits.insert(lit);
    }
    Clause(const set<Literal *, LiteralPtrLess> &lits) : lits(lits) {}

    set<Literal *, LiteralPtrLess> lits;
};

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

    RRuleInfo RRule1();

    vector<Clause *> clauses;
};

void print_clause(Clause &c);
