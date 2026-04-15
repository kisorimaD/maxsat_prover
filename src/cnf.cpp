#include "cnf.h"
#include <iostream>
#include <algorithm>
#include <set>
#include <assert.h>
#include <math.h>
#include <string>
#include <functional>
#include <unordered_set>
#include <fstream>
#include <limits>

// #include <fstream>

using namespace std;

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 2;
double C;

Literal UNKNOWN_LITERAL = Literal();
Literal UNKNOWN_NOT_EMPTY_LITERAL = Literal(1, false);

vector<LiteralDegType> POSSIBLE_LITERALS;

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

        int max_val = (*this).clauses.size() - count_set_bits(no_clauses_mask[mask]); // YES + "?"

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

            if (count_set_bits(clauses_mask[other_mask]) >= max_val)
            {
                if ((*this).clauses.size() - no_clauses_mask[other_mask] <= clauses_mask[mask] && other_mask > mask)
                {
                    continue;
                }

                is_subset = true;
                break;
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]))
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

bool get_next_partition(std::vector<int> &c, int k)
{
    int i = c.size() - 1;

    while (i >= 0)
    {
        int mx = -1;
        for (int j = 0; j < i; j++)
            if (c[j] > mx)
                mx = c[j];

        int limit = mx + 1;
        if (k != -1 && limit > k - 1)
            limit = k - 1;

        if (c[i] < limit)
        {
            c[i]++;
            return true;
        }

        c[i] = 0;
        i--;
    }

    return false;
}

vector<string> valid_3_partitions;
int partition_ind;

bool get_next_3_partition_fast(std::vector<int> &c, vector<bool> &mask_of_reduced_clauses)
{
    if (partition_ind == valid_3_partitions.size())
        return false;

    int skip_cnt = 0;
    for (int i = 0; i < 8; ++i)
    {
        if (!mask_of_reduced_clauses[i])
            c[skip_cnt++] = valid_3_partitions[partition_ind][i] - '0';
    }

    partition_ind++;

    return true;
}

vector<int> CNF::branch_group(vector<int> ids, int max_partitions)
{
    partition_ind = 0;

    int k = ids.size();

    bool is_3_case = false; // Случай, когда формулу группируют по 3 переменным. Для него предподсчитаны все разбиения
    if (k == 3)
    {
        is_3_case = true;
    }

    set<int> using_ids;
    for (Clause *cl : this->clauses)
    {
        for (Literal *l : cl->lits)
        {
            if (l->id != UNKNOWN_LITERAL.id && l->id != UNKNOWN_NOT_EMPTY_LITERAL.id)
            {
                using_ids.insert(l->id);
            }
        }
    }
    int kreal = using_ids.size(); // Реальное количество литералов, которое мы используем

    vector<int> branch;

    // set <int> true_clauses_masks;
    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses, no_clauses_mask);

    vector<bool> mask_of_reduced_subsets(1 << k, true); // Маска подстановок, которые удалили
    vector<int> rclauses;                               // Маски выполненных клоз (YES) для каждой оставшейся подстановки [rcnt]
    vector<int> no_clauses;
    vector<int> masks; // Маска подстановки для оставшихся подстановок

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        bool is_subset = false;

        int max_val = (*this).clauses.size() - count_set_bits(no_clauses_mask[mask]); // YES + "?"

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

            if (count_set_bits(clauses_mask[other_mask]) >= max_val)
            {
                if (((*this).clauses.size() - count_set_bits(no_clauses_mask[other_mask]) <= count_set_bits(clauses_mask[mask])) && (other_mask > mask))
                {
                    continue;
                }

                is_subset = true;
                break;
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]))
            {
                is_subset = true;
                break;
            }
        }

        if (!is_subset)
        {
            rclauses.push_back(clauses_mask[mask]);
            no_clauses.push_back(no_clauses_mask[mask]);
            masks.push_back(mask);
            mask_of_reduced_subsets[mask] = false;
        }
    }

    int rcnt = rclauses.size(); // Количество оставшихся подстановок, после удаления тех, которые полностью входят в другие

    double mn_factor = 100000;
    vector<int> mn_branch;

    vector<int> cs(rcnt, 0);

    vector<int> mn_partition(rcnt, -1);

    vector<int> now_branch;

    do
    {
        bool got_zero = false;

        now_branch.clear();

        bool no_merge_config = false;

        for (int c = 0; c < rcnt; ++c)
        {
            bool has_class = false;

            int gclauses = 0;
            int gnoclauses = 0;

            int partition_size = 0;

            vector<int> clause_used((*this).clauses.size(), -1);
            vector<bool> clause_only_no((*this).clauses.size(), true);

            for (int i = 0; i < rcnt; ++i)
            {
                if (cs[i] == c)
                {
                    partition_size++;

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

                    for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                    {
                        if (((rclauses[i] >> cl) & 1) == 0)
                        {
                            if (clause_used[cl] == -1)
                            {
                                clause_used[cl] = i;
                            }
                            else
                            {
                                clause_used[cl] = -2;
                            }
                        }
                        else
                        {
                            clause_only_no[cl] = false;
                        }

                        if ((no_clauses[i] >> cl) & 1)
                        {
                            clause_used[cl] = -2;
                        }
                    }

                    has_class = true;
                }
            }

            if (!has_class)
                continue;

            bool cant_merge = false;

            // Проверка на то, можем ли мы сгруппировать данный класс
            // Проверка с помощью афинного пространства

            if (!is_3_case) // В случае 3 переменных всё предподсчитано и проверено
            {
                set<int> masks_set;
                for (int i = 0; i < rcnt; ++i)
                {
                    if (cs[i] == c)
                    {
                        masks_set.insert(masks[i]);
                    }
                }

                for (int i = 0; i < rcnt; ++i)
                {
                    if (cs[i] != c)
                        continue;

                    for (int j = i + 1; j < rcnt; ++j)
                    {
                        if (cs[j] != c)
                            continue;

                        for (int z = j + 1; z < rcnt; ++z)
                        {
                            if (cs[z] != c)
                                continue;

                            int sup_mask = masks[i] ^ masks[j] ^ masks[z];

                            if (masks_set.find(sup_mask) == masks_set.end())
                            {
                                cant_merge = true;
                                break;
                            }
                        }

                        if (cant_merge)
                            break;
                    }

                    if (cant_merge)
                        break;
                }

                if (cant_merge)
                {
                    no_merge_config = true;
                    break;
                }
            }

            bool cross_reduce = false;
            int cross_size = -1; // Количество невыполненных клоз в остальных кроме cross подстановках (не считая клоз, которые полностью не выполнены)

            if (partition_size >= 2)
            {
                int cross_row = -1;
                bool found_cross = false;

                for (int i = 0; i < rcnt; ++i)
                {
                    if (cs[i] != c)
                        continue;

                    bool valid_cross = true;

                    int lastz = 0;
                    int zcnt = 0; // количество невыполненных клоз
                    for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                    {
                        if (((rclauses[i] >> cl) & 1) == 0 && !clause_only_no[cl])
                        {
                            // valid_cross = false;
                            zcnt++;
                            lastz = cl;
                            // break;
                        }
                    }

                    if (zcnt == 1)
                    {
                        if (((no_clauses[i] >> lastz) & 1) == 1)
                        {
                            // На месте cross стоит не ?, а NO. В таком случае мы не можем применить cross_reduce
                            valid_cross = false;
                            continue;
                        }

                        // Проверяем единицы на столбце с одним нулём
                        for (int sub = 0; sub < rcnt; ++sub)
                        {
                            if (cs[sub] != c || sub == i)
                                continue;

                            if (((rclauses[sub] >> lastz) & 1) == 0)
                            {
                                valid_cross = false;
                                break;
                            }
                        }
                    }
                    else
                    {
                        valid_cross = false;
                    }

                    if (valid_cross)
                    {
                        found_cross = true;
                        cross_row = i;
                        break;
                    }
                }

                if (found_cross)
                {
                    // Если можно выполнить cross_reduce, то все остальные подстановки - одинаковые
                    cross_reduce = true;

                    for (int cl = 0; cl < (int)this->clauses.size(); ++cl) // Перебираем все клозы
                    {
                        char clause_result = '#'; // не инициализированное значение клозы

                        for (int i = 0; i < rcnt; ++i) // Пробегаем по всем подстановкам из нашего разбиения без cross_row
                        {
                            if (cs[i] != c || i == cross_row)
                            {
                                continue;
                            }

                            if (((rclauses[cross_row] >> cl) & 1) != ((rclauses[i] >> cl) & 1))
                            {
                                cross_size++;
                            }

                            char now_result = (((rclauses[i] >> cl) & 1) == 0 ? 'N' : 'Y');
                            if (clause_result == '#')
                            {
                                clause_result = now_result;
                            }
                            else
                            {
                                if (clause_result != now_result)
                                {
                                    cross_reduce = false;
                                    break;
                                }
                            }
                        }

                        if (!cross_reduce)
                            break;
                    }
                }
            }

            bool lemma3_2partition = false;
            bool var2reduce = false;
            int D = 0;

            // bool lemma3_general = false; // Лемма 3 для группировки не на 2 подстановки

            // bool lemma2_general = false;
            // int lemma2_i = 0;
            // int lemma2_D = 0;

            vector<int> best_extra_branch;
            double best_extra_factor = C;

            if (partition_size == 2)
            {
                // Пытаемся найти 2- или 3- переменную (2- переменная даст +1, 3- переменная +(1, 8) по Лемме 3)
                // Перебираемся по выполненным клозам - в новой формуле единственная переменная будет стоять там, где у двух подстановок различаются значения в клозе

                int clause_result_xor_mask = 0; // XOR Маска выполненных клоз для данной группы

                for (int i = 0; i < rcnt; ++i)
                {
                    if (cs[i] != c)
                        continue;

                    clause_result_xor_mask ^= rclauses[i];
                }
                // Единица будет стоять только на тех местах, где значение отличается, это нам и нужно

                int var_count = count_set_bits(clause_result_xor_mask); // Вхождение единственной переменной (так как группировка по двум подстановкам она будет единственной)

                if (var_count == 3)
                {
                    lemma3_2partition = true;
                    // Вообще по Лемме 3 можно побренчить на {1, t}, t:= max(8, 7 + 2|D|), где D - это клоза с ¬x если x - (2, 1)
                    // Давайте посмотрим сколько переменных мы точно знаем из нужной клозы

                    int first_cnt = 0, second_cnt = 0;
                    int first_last_clause = -1, second_last_clause = -1;

                    for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                    {
                        if (((clause_result_xor_mask >> cl) & 1) == 1)
                        {
                            for (int sub = 0; sub < rcnt; ++sub)
                            {
                                if (cs[sub] != c)
                                    continue;

                                if (((rclauses[sub] >> cl) & 1) == 1)
                                {
                                    first_cnt++;
                                    first_last_clause = cl;
                                }
                                else
                                {
                                    second_cnt++;
                                    second_last_clause = cl;
                                }

                                break;
                            }
                        }
                    }

                    assert(first_cnt == 1 || second_cnt == 1);

                    // Если мы сужаемся на partition_size == 2, то у нас остается всего одна переменная

                    if (first_cnt == 1)
                    {
                        D = ((this->clauses[first_last_clause]->lits.find(&UNKNOWN_NOT_EMPTY_LITERAL) != this->clauses[first_last_clause]->lits.end()) ? 1 : 0);
                    }
                    else if (second_cnt == 1)
                    {
                        D = ((this->clauses[second_last_clause]->lits.find(&UNKNOWN_NOT_EMPTY_LITERAL) != this->clauses[second_last_clause]->lits.end()) ? 1 : 0);
                    }
                    // if (first_cnt == 1)
                    // {
                    //     D = (this->clauses[first_last_clause]->lits.size());

                    //     if (this->clauses[first_last_clause]->lits.find(&UNKNOWN_LITERAL) != this->clauses[first_last_clause]->lits.end())
                    //     {
                    //         D--;

                    //         // if (D == 0)
                    //         //     D = 1;
                    //     }
                    // }
                    // else if (second_cnt == 1)
                    // {
                    //     D = (this->clauses[second_last_clause]->lits.size());

                    //     if (this->clauses[second_last_clause]->lits.find(&UNKNOWN_LITERAL) != this->clauses[second_last_clause]->lits.end())
                    //     {
                    //         D--;

                    //         // if (D == 0)
                    //         //     D = 1;
                    //     }
                    // }
                }
                else if (var_count == 2)
                {
                    var2reduce = true;
                    // Заметим, что в таком случае эти 2 клозы не могут быть одинаковыми, т.к. иначе одну из них бы удалили, так как она входит в другую (с YES)
                    // То есть если при замене мы получаем две клозы с x мы понимаем, что одна из подстановок была изначально хуже другой и не должна была существовать
                }
            }

            if (partition_size > 2)
            {
                // Пытаемся найти переменные с 3 вхождениями (Лемма 3)
                // и (i,1)-переменные (Лемма 2) среди активных клоз

                map<int, pair<int, int>> var_counts; // id -> {pos_count, neg_count}

                for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                {
                    if (((gclauses >> cl) & 1) == 0 && ((gnoclauses >> cl) & 1) == 0)
                    {
                        Clause *c_ptr = this->clauses[cl];

                        if (c_ptr->empty)
                            continue;

                        for (Literal *l : c_ptr->lits)
                        {
                            if (l->id != UNKNOWN_LITERAL.id && l->id != UNKNOWN_NOT_EMPTY_LITERAL.id)
                            {
                                if (l->inv)
                                    var_counts[l->id].second++;
                                else
                                    var_counts[l->id].first++;
                            }
                        }
                    }
                }

                int lemma3_singletons_cnt = 0;
                for (auto const &[id, counts] : var_counts)
                {
                    int pos = counts.first;
                    int neg = counts.second;
                    if (pos + neg == 3 && ((pos == 2 && neg == 1) || (pos == 1 && neg == 2)))
                    {
                        lemma3_singletons_cnt++;
                    }
                }

                for (auto const &[id, counts] : var_counts)
                {
                    int pos = counts.first;
                    int neg = counts.second;

                    // ---------- Лемма 3 ----------
                    if (pos + neg == 3 && ((pos == 2 && neg == 1) || (pos == 1 && neg == 2)))
                    {
                        bool need_inv = (pos == 1 ? false : true);
                        int local_D = 0;
                        bool found_clause = false;

                        for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                        {
                            if (((gclauses >> cl) & 1) == 0 && ((gnoclauses >> cl) & 1) == 0)
                            {
                                Clause *c_ptr = this->clauses[cl];
                                if (c_ptr->empty)
                                    continue;

                                bool found_target = false;
                                for (Literal *l : c_ptr->lits)
                                {
                                    if (l->id == id && l->inv == need_inv)
                                    {
                                        found_target = true;
                                        break;
                                    }
                                }

                                if (!found_target)
                                    continue;

                                local_D = (int)c_ptr->lits.size() - 1;
                                if (c_ptr->lits.find(&UNKNOWN_LITERAL) != c_ptr->lits.end())
                                    local_D--;

                                found_clause = true;
                                break;
                            }
                        }

                        // if (found_clause)
                        // {
                        //     vector<int> cand = {1, max(8, 7 + 2 * local_D)};
                        //     double cand_factor = branching_factor(cand);

                        //     if (cand_factor < best_extra_factor)
                        //     {
                        //         best_extra_factor = cand_factor;
                        //         best_extra_branch = cand;
                        //     }
                        // }

                        if (found_clause)
                        {
                            vector<int> cand;

                            if (lemma3_singletons_cnt >= 2)
                            {
                                // double Lemma 3: вместо (1,8) используем (2,9,8)
                                cand = {2, 9, 8};
                            }
                            else
                            {
                                cand = {1, max(8, 7 + 2 * local_D)};
                            }

                            double cand_factor = branching_factor(cand);

                            if (cand_factor < best_extra_factor)
                            {
                                best_extra_factor = cand_factor;
                                best_extra_branch = cand;
                            }
                        }

                    }

                    // ---------- Лемма 2 ----------
                    if (pos > 0 && neg > 0 && (pos == 1 || neg == 1))
                    {
                        bool minority_inv = (neg == 1); // unique opposite clause contains ~x if neg==1, else x
                        int local_i = max(pos, neg);
                        int local_D = -1;

                        for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                        {
                            if (((gclauses >> cl) & 1) == 0 && ((gnoclauses >> cl) & 1) == 0)
                            {
                                Clause *c_ptr = this->clauses[cl];
                                if (c_ptr->empty)
                                    continue;

                                bool found_target = false;
                                for (Literal *l : c_ptr->lits)
                                {
                                    if (l->id == id && l->inv == minority_inv)
                                    {
                                        found_target = true;
                                        break;
                                    }
                                }

                                if (!found_target)
                                    continue;

                                local_D = 0;
                                for (Literal *l : c_ptr->lits)
                                {
                                    if (l->id == UNKNOWN_LITERAL.id)
                                        continue;

                                    if (l->id == UNKNOWN_NOT_EMPTY_LITERAL.id)
                                    {
                                        local_D += 1; // ?+ гарантирует хотя бы один другой литерал
                                        continue;
                                    }

                                    if (l->id != id)
                                        local_D++;
                                }

                                break;
                            }
                        }

                        if (local_D >= 0)
                        {
                            vector<int> cand = {local_i, 1 + 2 * local_D};
                            double cand_factor = branching_factor(cand);

                            if (cand_factor < best_extra_factor)
                            {
                                best_extra_factor = cand_factor;
                                best_extra_branch = cand;
                            }
                        }
                    }
                }
            }

            if (has_class)
            {
                if (gclauses == 0 && gnoclauses == 0)
                {
                    got_zero = true;
                    break;
                }
                // now_branch.push_back(count_set_bits(gclauses) + count_set_bits(gnoclauses) + abc_reduced);
                int basic_reduce = count_set_bits(gclauses) + count_set_bits(gnoclauses);
                // now_branch.push_back(basic_reduce + ());

                // double best_branch_factor = branching_factor();

                // lemma3_2partition = false;

                if (var2reduce)
                {
                    now_branch.push_back(basic_reduce + 1);
                }
                else if (cross_reduce && cross_size <= 2)
                {
                    if (cross_size == 1)
                        now_branch.push_back(basic_reduce + 1);
                    else if (cross_size == 2)
                    {
                        now_branch.push_back(basic_reduce + 1);
                        now_branch.push_back(basic_reduce + 8);
                    }
                }
                else if (lemma3_2partition)
                {
                    now_branch.push_back(basic_reduce + 1);
                    // now_branch.push_back(basic_reduce + 8); // max(8, 7 + 2 * D));
                    now_branch.push_back(basic_reduce + max(8, 7 + 2 * D));
                }
                else if (!best_extra_branch.empty())
                {
                    for (int x : best_extra_branch)
                    {
                        now_branch.push_back(basic_reduce + x);
                    }
                }
                else
                {
                    now_branch.push_back(basic_reduce);
                }
            }
        }

        if (got_zero || no_merge_config)
        {
            continue;
        }

        double now_factor = branching_factor(now_branch);

        if (now_factor < mn_factor)
        {
            mn_factor = now_factor;
            mn_branch = now_branch;
            mn_partition = cs;
        }

    } while (is_3_case ? get_next_3_partition_fast(cs, mask_of_reduced_subsets) : get_next_partition(cs, max_partitions));

    return mn_branch;
}

// vector<int> CNF::

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
    if (a.empty() || (a.size() == 1 && a[0] == 0))
    {
        return 100.0;
    }
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
            cout << " ∨ ";

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

unordered_set<string> *used;

void preprocess(int maximum_clause_size)
{
    used = (new unordered_set<string>());
    ID2VAR[0] = "?";
    VAR2ID["?"] = 0;
    ID2VAR[1] = "?+";
    VAR2ID["?+"] = 1;

    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = maximum_clause_size;

    POSSIBLE_LITERALS = {
        {1, 3, SINGLETON},
        {3, 1, SINGLETON},
        {2, 2, ANY},
        {3, 2, ANY},
        {2, 3, ANY},
        {3, 1, SINGLETON},
        {4, 1, SINGLETON}};

    ifstream infile("groups3.txt");
    if (!infile.is_open())
    {
        cerr << "Couldn't open file with groups" << endl;
        return;
    }

    int N;

    if (infile.is_open())
    {
        infile >> N;
        string line;
        getline(infile, line);
        for (int i = 0; i < N; ++i)
        {
            infile >> line;
            if (!line.empty())
                valid_3_partitions.push_back(line);
        }
        infile.close();

        cout << "Загружено " << valid_3_partitions.size() << " разбиений\n\n";
    }
}

string join(vector<string> a, string del)
{
    string ans;
    for (int i = 0; i < (int)a.size(); ++i)
    {
        ans += a[i];
        if (i < (int)a.size() - 1)
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
    for (int i = 0; i < (int)perm.size(); ++i)
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

// set<string> used;

vector<CNF *> add_new_var_universal(CNF *cnf, string v_name, int i, int j, LitType type, int pos = -1, bool only_pos = false)
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

                    bool var_skip = false;

                    for (int k = 0; k < cnf_size; ++k)
                    {

                        if (only_pos && pos == k)
                        {
                            if (m[k] && xm[xm_ind])
                            {
                            }
                            else
                            {
                                var_skip = true;
                                break;
                            }
                        }

                        if (m[k])
                        {
                            if (now_cnf->clauses[k]->lits.find(&UNKNOWN_LITERAL) != now_cnf->clauses[k]->lits.end() || now_cnf->clauses[k]->lits.find(&UNKNOWN_NOT_EMPTY_LITERAL) != now_cnf->clauses[k]->lits.end())
                            {

                                if (now_cnf->clauses[k]->lits.find(&UNKNOWN_NOT_EMPTY_LITERAL) != now_cnf->clauses[k]->lits.end())
                                {
                                    now_cnf->clauses[k]->lits.erase(&UNKNOWN_NOT_EMPTY_LITERAL);
                                    now_cnf->clauses[k]->lits.insert(&UNKNOWN_LITERAL);
                                }

                                if (xm[xm_ind++])
                                {
                                    now_cnf->clauses[k]->lits.insert(new_lit);
                                }
                                else
                                {
                                    now_cnf->clauses[k]->lits.insert(new_lit_neg);
                                }
                            }
                            else
                            {
                                var_skip = true;
                                break;
                            }
                        }
                    }

                    if (var_skip)
                    {
                        continue;
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

                    if (MaxSATSettings.MAXIMUM_CLAUSE_SIZE != -1)
                    {
                        bool too_many_lits = false;

                        for (Clause *c : now_cnf->clauses)
                        {
                            if (c->lits.size() > MaxSATSettings.MAXIMUM_CLAUSE_SIZE + 1 || (c->lits.size() == MaxSATSettings.MAXIMUM_CLAUSE_SIZE + 1 && c->lits.find(&UNKNOWN_LITERAL) == c->lits.end()))
                            {
                                too_many_lits = true;
                                break;
                            }
                        }

                        if (too_many_lits)
                            continue;

                        for (Clause *c : now_cnf->clauses)
                        {
                            if (c->lits.size() == MaxSATSettings.MAXIMUM_CLAUSE_SIZE + 1)
                            {
                                c->lits.erase(&UNKNOWN_LITERAL);
                            }
                        }
                    }

                    string now_cnf_str = cnf_to_max_string(now_cnf);

                    if (used->find(now_cnf_str) == used->end())
                    {
                        ans.push_back(now_cnf);
                        used->insert(now_cnf_str);
                    }

                    // ans.push_back(now_cnf);

                } while (prev_permutation(xm.begin(), xm.end()));
            }

        } while (prev_permutation(m.begin(), m.end()));
    }

    return ans;
}

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type)
{
    return add_new_var_universal(cnf, v_name, i, j, type);
}

vector<CNF *> add_new_var_in_place(CNF *cnf, string v_name, const std::function<int(CNF *)> &need_index_func, vector<LiteralDegType> variants)
{
    int pos = need_index_func(cnf);

    vector<CNF *> ans;

    // auto new_vars = add_new_var(cnf, var_name, i, j, new_type);
    // new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
    // copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());

    for (LiteralDegType l : variants)
    {
        auto new_vars = add_new_var_universal(cnf, v_name, l.i, l.j, l.type, pos, true);
        ans.resize(ans.size() + new_vars.size());
        copy(new_vars.begin(), new_vars.end(), ans.rbegin());
    }

    CNF *cnf_empty_space = new CNF(*cnf);

    if (pos < cnf_empty_space->clauses.size() && cnf_empty_space->clauses[pos]->lits.find(&UNKNOWN_LITERAL) != cnf_empty_space->clauses[pos]->lits.end())
    {
        cnf_empty_space->clauses[pos]->lits.erase(&UNKNOWN_LITERAL);
    }

    if (cnf_empty_space->clauses.size() != 0)
        ans.push_back(cnf_empty_space);

    return ans;
}

// Функция возвращает пару {CNF_с_пустотой, CNF_с_непустотой(?+)}
pair<CNF *, CNF *> empty_divide(CNF *cnf)
{
    pair<CNF *, CNF *> best_split = {nullptr, nullptr};
    double min_worst_factor = std::numeric_limits<double>::infinity();

    vector<int> ids;

    for (auto p : ID2VAR)
    {
        if (p.first != UNKNOWN_LITERAL.id && p.first != UNKNOWN_NOT_EMPTY_LITERAL.id)
        {
            ids.push_back(p.first);
        }
    }

    for (int i = 0; i < (int)cnf->clauses.size(); ++i)
    {
        Clause *c = cnf->clauses[i];

        // Ищем клозу, в которой есть обычный '?'
        if (c->lits.find(&UNKNOWN_LITERAL) != c->lits.end())
        {

            // 1. Создаем ветку, где '?' означает пустоту (просто удаляем '?')
            CNF *cnf_empty = new CNF(*cnf);
            cnf_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);

            // 2. Создаем ветку, где '?' означает минимум 1 литерал (заменяем на '?+')
            CNF *cnf_not_empty = new CNF(*cnf);
            cnf_not_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);
            cnf_not_empty->clauses[i]->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);

            // Оцениваем обе ветки.
            // Примечание: предполагается, что xiao_branch возвращает вектор редукций
            // (или вызывает group_branch внутри себя для поиска лучшего ветвления).
            double factor_empty = min(branching_factor(cnf_empty->xiao_branch(1, "x")), branching_factor(cnf_empty->branch_group(ids)));
            double factor_not_empty = min(branching_factor(cnf_not_empty->xiao_branch(1, "x")), branching_factor(cnf_not_empty->branch_group(ids)));

            // Худший случай при данном разбиении (мы вынуждены будем пойти в худшую из двух веток)
            double worst_factor = max(factor_empty, factor_not_empty);

            if (worst_factor < min_worst_factor)
            {
                min_worst_factor = worst_factor;

                // Очищаем предыдущий лучший вариант, чтобы не было утечек памяти
                if (best_split.first)
                    delete best_split.first;
                if (best_split.second)
                    delete best_split.second;

                best_split = {cnf_empty, cnf_not_empty};
            }
            else
            {
                // Если вариант не лучше, сразу удаляем созданные копии
                delete cnf_empty;
                delete cnf_not_empty;
            }
        }
    }

    return best_split;
}