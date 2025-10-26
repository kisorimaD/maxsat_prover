#include "cnf.h"
#include <iostream>
#include <algorithm>
#include <set>
#include <assert.h>
#include <math.h>
#include <string>

using namespace std;

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 1;
Literal UNKNOWN_LITERAL = Literal();

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

bool is_A_subset_of_B(int A, int B)
{
    int A_without_B = (A | B) ^ B;

    return A_without_B == 0;
}

void calculate_variants(CNF &cnf, vector<int> &ids, vector<int> &clauses_mask, vector<int> &reduced_clauses, vector<int> &no_clauses_mask)
{

    int k = ids.size();

    map<int, int> id2ind;

    for (int i = 0; i < k; ++i)
        id2ind[ids[i]] = i;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        int reduced = 0;

        int tc_mask = 0;
        int no_mask = 0;

        // for (Clause *c : clauses)
        for (int clause_ind = 0; clause_ind < (int)cnf.clauses.size(); ++clause_ind)
        {
            Clause *c = cnf.clauses[clause_ind];

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

            if (find_1)
            {
                tc_mask ^= (1 << clause_ind);
            }

            if (!find_1 && !find_another_literal)
            {
                no_mask ^= (1 << clause_ind);
            }
        }

        clauses_mask[mask] = tc_mask;
        no_clauses_mask[mask] = no_mask;
        reduced_clauses[mask] = reduced;
    }
}

vector<int> CNF::branch(vector<int> ids)
{

    int k = ids.size();

    vector<int> branch;

    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses, no_clauses_mask);

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        bool is_subset = false;

        for (int other_mask = 0; other_mask < (1 << k); ++other_mask)
        {
            if (mask == other_mask)
                continue;

            if (clauses_mask[mask] == clauses_mask[other_mask])
            {
                if (other_mask >= mask)
                {
                    continue;
                }
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]) && no_clauses_mask[mask] == no_clauses_mask[other_mask])
            {
                is_subset = true;
                break;
            }
        }

        if (!is_subset)
        {
            branch.push_back(reduced_clauses[mask]);
        }
    }

    return branch;
}

bool get_next_product(vector<int> &cs)
{
    int i = cs.size() - 1;

    while (i)
    {
        if (cs[i] < i)
        {
            cs[i]++;
            return true;
        }
        else
        {
            cs[i] = 0;
            i--;
        }
    }
    return false;
}

int count_set_bits(int n)
{
    int cnt = 0;
    while (n)
    {
        n &= (n - 1);
        cnt++;
    }
    return cnt;
}

vector<int> CNF::branch_group(vector<int> ids)
{
    int k = ids.size();

    vector<int> branch;

    // set <int> true_clauses_masks;
    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses, no_clauses_mask);

    vector<int> rclauses;
    vector<int> no_clauses;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        bool is_subset = false;

        for (int other_mask = 0; other_mask < (1 << k); ++other_mask)
        {
            if (mask == other_mask)
                continue;

            if (clauses_mask[mask] == clauses_mask[other_mask])
            {
                if (other_mask >= mask)
                {
                    continue;
                }
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]) && no_clauses_mask[mask] == no_clauses_mask[other_mask])
            {
                is_subset = true;
                break;
            }
        }

        if (!is_subset)
        {
            rclauses.push_back(clauses_mask[mask]);
            no_clauses.push_back(no_clauses_mask[mask]);
        }
    }

    int rcnt = rclauses.size();

    double mn_factor = 100000;
    vector<int> mn_branch;

    vector<int> cs(rcnt, 0);

    vector<int> now_branch;

    do
    {
        bool got_zero = false;

        now_branch.clear();

        for (int c = 0; c < rcnt; ++c)
        {
            bool has_class = false;

            int gclauses = 0;
            int gnoclauses = 0;

            for (int i = 0; i < rcnt; ++i)
            {
                if (cs[i] == c)
                {
                    if (!has_class)
                    {
                        gclauses = rclauses[i];
                        gnoclauses = no_clauses[i];
                    }
                    else
                    {
                        gclauses &= rclauses[i];
                        gnoclauses &= no_clauses[i];
                    }

                    has_class = true;
                }
            }

            if (has_class)
            {
                if (gclauses == 0 && gnoclauses == 0)
                {
                    got_zero = true;
                    break;
                }
                now_branch.push_back(count_set_bits(gclauses) + count_set_bits(gnoclauses));
            }
        }

        if (got_zero)
        {
            continue;
        }

        double now_factor = branching_factor(now_branch);

        if (now_factor < mn_factor)
        {
            mn_factor = now_factor;
            mn_branch = now_branch;
        }

    } while (get_next_product(cs));

    return mn_branch;
}

double f_value(double x, const vector<int> &a)
{ // compute sum_i x^{-a_i} - 1
    long double s = 0.0L;
    for (int ai : a)
    {
        s += powl((long double)x, (long double)(-ai));
    }
    return (double)(s - 1.0L);
}

map<vector<int>, double> branching_factor_cache;

double branching_factor(const vector<int> &a, double tol)
{
    vector<int> b = a;
    sort(b.begin(), b.end());

    if (branching_factor_cache.count(b) != 0)
    {
        return branching_factor_cache[b];
    }

    double low = 1.0 - 1e-14;
    double high = 2.5;

    auto f = [&](double x)
    { return f_value(x, a); };

    for (int iter = 0; iter < 80; ++iter)
    {
        double fv = f(high);
        if (fv < 0.0)
            break;
        high *= 1.5;
        if (high > 1e8)
        {
            string v_str = "( ";
            for (int n : a)
            {
                v_str += (to_string(n) + " ");
            }
            v_str += ")";
            throw runtime_error("Cannot bracket root: high grew too large. Branch: " + v_str);
        }
    }

    double fl = f(low);
    double fh = f(high);
    if (!(fl > 0.0 && fh < 0.0))
    {
        // numerical safeguard: if fl already <= 0 (rare), move low slightly toward 1
        if (fl <= 0.0)
            low = 1.0 + 1e-16, fl = f(low);
        if (!(fl > 0.0 && fh < 0.0))
        {
            // as ultimate fallback, try expanding high more
            for (int iter = 0; iter < 200 && fh >= 0.0; ++iter)
            {
                high *= 1.5;
                fh = f(high);
                if (high > 1e12)
                    break;
            }
            if (!(fl > 0.0 && fh < 0.0))
            {
                string v_str = "( ";
                for (int n : a)
                {
                    v_str += (to_string(n) + " ");
                }
                v_str += ")";
                throw runtime_error("Failed to bracket root (fl, fh) = (" + to_string(fl) + ", " + to_string(fh) + ") " + v_str);
            }
        }
    }

    for (int iter = 0; iter < 2000; ++iter)
    {
        double mid = 0.5 * (low + high);
        double fm = f(mid);
        if (fm > 0.0)
            low = mid;
        else
            high = mid;
        if (fabs(high - low) < tol * max(1.0, mid))
            break;
    }

    branching_factor_cache[b] = 0.5 * (low + high);

    return 0.5 * (low + high);
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

string join(vector<string> a, string del)
{
    string ans;
    for (int i = 0; i < a.size(); ++i)
    {
        ans += a[i];
        if (i < a.size() - 1)
            ans += del;
    }
    return ans;
}

string cnf_to_string(CNF *cnf)
{
    vector<string> clauses_str;
    for (auto clause : cnf->clauses)
    {
        vector<string> lits_str;
        for (auto lit : clause->lits)
        {
            lits_str.push_back((lit->inv ? "~" : "=") + to_string(lit->id));
        }
        sort(lits_str.begin(), lits_str.end());
        string clause_str = "(" + join(lits_str, "∨") + ")";
        clauses_str.push_back(clause_str);
    }
    sort(clauses_str.begin(), clauses_str.end());
    return join(clauses_str, "∧");
}

string cnf_to_max_string(CNF *cnf)
{
    vector<int> perm(ID_COUNTER - 1);
    for (int i = 0; i < perm.size(); ++i)
    {
        perm[i] = i + 1;
    }

    string max_str;

    vector<string> clauses_str;

    do
    {
        clauses_str.clear();
        for (auto clause : cnf->clauses)
        {
            vector<string> lits_str;
            for (auto lit : clause->lits)
            {
                lits_str.push_back((lit->inv ? "~" : "=") + to_string(lit->id == 0 ? 0 : perm[lit->id - 1]));
            }
            sort(lits_str.begin(), lits_str.end());
            string clause_str = "(" + join(lits_str, "∨") + ")";
            clauses_str.push_back(clause_str);
        }
        sort(clauses_str.begin(), clauses_str.end());
        string now_str = join(clauses_str, "∧");

        if (now_str > max_str)
        {
            max_str = now_str;
        }

    } while (next_permutation(perm.begin(), perm.end()));

    // cout << "---------\n";
    // print_cnf(*cnf);
    // cout << max_str << endl;

    return max_str;
}

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type)
{
    // a + b = s
    // В 0 <= a <= i клозах литерал встречается с x
    // В 0 <= b <= j клозах он встречается с ~x
    // Остальное в новых клозах

    set<string> used;

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
                        if (m[k] && now_cnf->clauses[k]->lits.find(&UNKNOWN_LITERAL) != now_cnf->clauses[k]->lits.end())
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

                        if (k == 0 && !m[k])
                        {
                            now_cnf->clauses[0]->lits.erase(&UNKNOWN_LITERAL);
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

                    string now_cnf_str = cnf_to_max_string(now_cnf);

                    if (used.find(now_cnf_str) == used.end())
                    {
                        ans.push_back(now_cnf);
                        used.insert(now_cnf_str);
                    }

                    // ans.push_back(now_cnf);

                } while (prev_permutation(xm.begin(), xm.end()));
            }

        } while (prev_permutation(m.begin(), m.end()));
    }

    return ans;
}