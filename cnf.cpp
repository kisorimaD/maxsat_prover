#include "cnf.h"
#include <iostream>
#include <algorithm>
#include <set>
#include <assert.h>

using namespace std;

Literal::Literal()
{
    id = 0;
};

Literal::Literal(string var, bool is_inv)
{
    if (VAR2ID.count(var) != 0)
    {
        id = VAR2ID[var];
        inv = is_inv;
    }
    else
    {
        id = ID_COUNTER;
        ID_COUNTER++;

        ID2VAR[id] = var;
        VAR2ID[var] = id;

        inv = is_inv;
    }
}

Literal::Literal(int _id, bool is_inv)
{
    id = _id;
    inv = is_inv;
}

Literal Literal::neg() const
{
    return Literal(id, !inv);
}

vector<int> CNF::branch(vector<int> ids)
{
    // Строим таблицу истинностей

    int k = ids.size();

    map<int, int> id2ind;

    for (int i = 0; i < k; ++i)
        id2ind[ids[i]] = i;

    vector<int> branch(1 << k);

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        int reduced = 0;

        for (Clause *c : clauses)
        {
            bool find_another_literal = false;
            bool find_1 = false;

            for (Literal *l : c->lits)
            {
                if (id2ind.count(l->id) != 0)
                {
                    if (((mask >> id2ind[l->id]) & 1) ^ l->inv)
                    {
                        find_1 = true;
                        break;
                    }
                }
                else
                {
                    find_another_literal = true;
                }
            }

            if (find_1 || !find_another_literal)
            {
                reduced++;
            }
        }

        branch[mask] = reduced;
    }

    return branch;
}

void print_clause(Clause &c)
{
    int n = c.lits.size();

    if (n == 0)
    {
        cout << "( )";
        return;
    }

    cout << "( ";

    int i = 0;
    for (auto &lit : c.lits)
    {
        if (lit->inv)
        {
            cout << "¬";
        }
        cout << ID2VAR[lit->id];

        if (i != n - 1)
            cout << " ∧ ";

        i++;
    }

    cout << " )";
}

void print_cnf(CNF &cnf)
{
    for (Clause *c : cnf.clauses)
    {
        print_clause(*c);
    }
    cout << endl;
}

void preprocess()
{
    ID2VAR[0] = "?";
    VAR2ID["?"] = 0;
}

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type)
{
    // a + b = s
    // В 0 <= a <= i клозах литерал встречается с x
    // В 0 <= b <= j клозах он встречается с ~x
    // Остальное в новых клозах

    vector<CNF *> ans;

    Literal *new_lit = new Literal(v_name);
    Literal *new_lit_neg = new Literal(new_lit->id, !new_lit->inv);

    int cnf_size = cnf->clauses.size();

    vector<bool> m(cnf_size);

    for (int s = 0; s <= min(cnf_size, i + j); ++s)
    {
        fill(m.begin() + s, m.end(), false);
        fill(m.begin(), m.begin() + s, true);

        vector<bool> xm(s);

        do
        {
            for (int a = 0; a <= min(i, s); ++a)
            {
                if (type == SINGLETON && s != a)
                    continue;

                fill(xm.begin() + a, xm.end(), false);
                fill(xm.begin(), xm.begin() + a, true);

                do
                {
                    int xm_ind = 0;

                    CNF *now_cnf = new CNF(*cnf);

                    for (int k = 0; k < cnf_size; ++k)
                    {
                        if (m[k])
                        {
                            if (xm[xm_ind++])
                            {
                                now_cnf->clauses[k]->lits.insert(new_lit);
                            }
                            else
                            {
                                now_cnf->clauses[k]->lits.insert(new_lit_neg);
                            }
                        }
                    }

                    for (int k = 0; k < (i - a); ++k) // Добиваем остатки в новых клозах
                    {
                        vector<Literal *> new_clause_list = {new_lit, &UNKNOWN_LITERAL};
                        Clause *new_clause_x = new Clause(new_clause_list);
                        now_cnf->clauses.push_back(new_clause_x);
                    }

                    for (int k = 0; k < (j - (s - a)); ++k)
                    {
                        if (type == SINGLETON)
                        {
                            vector<Literal *> single_literal = {new_lit_neg};
                            Clause *new_clause_nx = new Clause(single_literal);
                            now_cnf->clauses.push_back(new_clause_nx);
                        }
                        else
                        {
                            vector<Literal *> new_clause_list = {new_lit_neg, &UNKNOWN_LITERAL};
                            Clause *new_clause_x = new Clause(new_clause_list);
                            now_cnf->clauses.push_back(new_clause_x);
                        }
                    }

                    ans.push_back(now_cnf);

                } while (prev_permutation(xm.begin(), xm.end()));
            }

        } while (prev_permutation(m.begin(), m.end()));
    }

    return ans;
}

void test_basics()
{
    Literal a("a");
    Literal b("b");

    Literal na = a.neg();
    vector<Literal *> vec_lits = {&a, &b, &na, &UNKNOWN_LITERAL};
    Clause c(vec_lits);
    Clause d = c;

    Literal nb = b.neg();

    d.lits.insert(&nb);

    print_clause(c);
    print_clause(d);

    Clause unk;

    print_clause(unk);
}

void test_three_vars()
{

    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    print_cnf(*with_x);

    cout << "Добавляем переменную y (2, 3)-литерал\n";

    vector<CNF *> with_y = add_new_var(with_x, "y", 3, 2, ANY);

    vector<CNF *> with_z;
    cout << with_y.size() << endl;

    for (CNF *br : with_y)
    {
        auto new_vars = add_new_var(br, "z", 3, 2, ANY);

        with_z.resize(with_z.size() + new_vars.size());
        copy(new_vars.begin(), new_vars.end(), with_z.rbegin());
    }

    cout << with_z.size() << endl;
}

void test_simple_branch()
{
    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    print_cnf(*with_x);

    Literal x = Literal("x");

    assert(x.id == 1);

    vector<int> b = with_x->branch({x.id});

    for (int f : b)
    {
        cout << f << " ";
    }
    cout << endl;
}

int main()
{
    preprocess();

    test_simple_branch();
}
