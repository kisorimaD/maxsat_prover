#include "cnf.h"
#include "cert_logger.h"

#include <algorithm>
#include <assert.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <math.h>
#include <set>
#include <string>
#include <unordered_set>

// #include <fstream>

using namespace std;

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 2;
double C;

Literal UNKNOWN_LITERAL = Literal();
Literal UNKNOWN_NOT_EMPTY_LITERAL = Literal(1, false);

vector<LiteralDegType> POSSIBLE_LITERALS;

Literal::Literal() { id = 0; };

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

Literal Literal::neg() const { return Literal(id, !inv); }

long long GLOBAL_NODE_ID_COUNTER = 0;

CNF::CNF()
{
    node_id = ++GLOBAL_NODE_ID_COUNTER;
}

CNF::CNF(CNF &cnf)
{
    node_id = ++GLOBAL_NODE_ID_COUNTER;
    clauses.resize(cnf.clauses.size());
    for (int i = 0; i < (int)clauses.size(); ++i)
    {
        clauses[i] = new Clause(*cnf.clauses[i]);
    }
}

std::vector<std::vector<int>> CNF::get_snapshot()
{
    std::vector<std::vector<int>> snap;
    for (Clause *c : clauses)
    {
        std::vector<int> cl_snap;
        for (Literal *l : c->lits)
        {
            if (l->id == 0 || l->id == 1)
                cl_snap.push_back(l->id);
            else
                cl_snap.push_back((l->inv ? -1 : 1) * l->id);
        }
        snap.push_back(cl_snap);
    }
    return snap;
}

bool is_A_subset_of_B(int A, int B)
{
    int A_without_B = (A | B) ^ B;

    return A_without_B == 0;
}

void calculate_variants(CNF &cnf, vector<int> &ids, vector<int> &clauses_mask,
                        vector<int> &reduced_clauses,
                        vector<int> &no_clauses_mask)
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
        for (int clause_ind = 0; clause_ind < (int)cnf.clauses.size();
             ++clause_ind)
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

ProofNode CNF::branch(vector<int> ids)
{

    int k = ids.size();

    vector<int> branch;

    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses,
                       no_clauses_mask);

    std::map<int, int> current_subsumptions;
    vector<int> valid_masks;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        bool is_subset = false;

        int max_val = (*this).clauses.size() -
                      count_set_bits(no_clauses_mask[mask]); // YES + "?"

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
                if ((*this).clauses.size() - no_clauses_mask[other_mask] <=
                        clauses_mask[mask] &&
                    other_mask > mask)
                {
                    continue;
                }

                current_subsumptions[mask] = other_mask;
                is_subset = true;
                break;
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]))
            {
                current_subsumptions[mask] = other_mask;
                is_subset = true;
                break;
            }
        }

        if (!is_subset)
        {
            branch.push_back(reduced_clauses[mask]);
            valid_masks.push_back(mask);
        }
    }

    ProofNode node(branch);
    node.formula_snapshot = this->get_snapshot();
    node.subsumptions = current_subsumptions;

    vector<int> full_partition(1 << k, -1);
    for (int i = 0; i < (int)branch.size(); ++i)
    {
        full_partition[valid_masks[i]] = i;
    }
    node.partition = full_partition;

    return node;
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

bool get_next_3_partition_fast(std::vector<int> &c,
                               vector<bool> &mask_of_reduced_clauses)
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

ProofNode CNF::branch_group(vector<int> ids, int max_partitions)
{
    partition_ind = 0;

    int k = ids.size();

    bool is_3_case = false; // Случай, когда формулу группируют по 3 переменным.
                            // Для него предподсчитаны все разбиения
    if (k == 3)
    {
        is_3_case = true;
    }

    set<int> using_ids;
    for (Clause *cl : this->clauses)
    {
        for (Literal *l : cl->lits)
        {
            if (l->id != UNKNOWN_LITERAL.id &&
                l->id != UNKNOWN_NOT_EMPTY_LITERAL.id)
            {
                using_ids.insert(l->id);
            }
        }
    }
    int kreal =
        using_ids.size(); // Реальное количество литералов, которое мы используем

    vector<int> branch;

    // set <int> true_clauses_masks;
    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses,
                       no_clauses_mask);

    vector<bool> mask_of_reduced_subsets(
        1 << k, true);    // Маска подстановок, которые удалили
    vector<int> rclauses; // Маски выполненных клоз (YES) для каждой оставшейся
                          // подстановки [rcnt]
    vector<int> no_clauses;
    vector<int> masks; // Маска подстановки для оставшихся подстановок

    std::map<int, int> current_subsumptions;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        bool is_subset = false;

        int max_val = (*this).clauses.size() -
                      count_set_bits(no_clauses_mask[mask]); // YES + "?"

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
                if (((*this).clauses.size() -
                         count_set_bits(no_clauses_mask[other_mask]) <=
                     count_set_bits(clauses_mask[mask])) &&
                    (other_mask > mask))
                {
                    continue;
                }

                current_subsumptions[mask] = other_mask;
                is_subset = true;
                break;
            }

            if (is_A_subset_of_B(clauses_mask[mask], clauses_mask[other_mask]))
            {
                current_subsumptions[mask] = other_mask;
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

    int rcnt = rclauses.size(); // Количество оставшихся подстановок, после
                                // удаления тех, которые полностью входят в другие

    double mn_factor = 100000;
    vector<int> mn_branch;

    vector<int> cs(rcnt, 0);

    vector<int> mn_partition(rcnt, -1);

    vector<int> now_branch;

    vector<GroupWitness> mn_witnesses;

    do
    {
        bool got_zero = false;
        now_branch.clear();
        bool no_merge_config = false;

        vector<GroupWitness> now_witnesses;

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
                vector<int> group_masks;
                for (int i = 0; i < rcnt; ++i)
                {
                    if (cs[i] == c)
                    {
                        group_masks.push_back(masks[i]);
                    }
                }

                int group_size = group_masks.size();

                // Быстрая проверка (Fast-fail):
                // Размер любого аффинного подпространства в GF(2) обязан быть степенью двойки (1, 2, 4, 8...).
                // Если это не так (например, 3 элемента), это точно не валидная группа.
                if (group_size > 0 && (group_size & (group_size - 1)) != 0)
                {
                    cant_merge = true;
                }
                else if (group_size >= 4) // Для 1 и 2 элементов замкнутость выполняется тривиально
                {
                    unordered_set<int> masks_set(group_masks.begin(), group_masks.end());

                    for (int i = 0; i < group_size && !cant_merge; ++i)
                    {
                        for (int j = i + 1; j < group_size && !cant_merge; ++j)
                        {
                            for (int z = j + 1; z < group_size && !cant_merge; ++z)
                            {
                                int sup_mask = group_masks[i] ^ group_masks[j] ^ group_masks[z];

                                if (masks_set.find(sup_mask) == masks_set.end())
                                {
                                    cant_merge = true;
                                }
                            }
                        }
                    }
                }

                if (cant_merge)
                {
                    no_merge_config = true;
                    break;
                }
            }

            bool cross_reduce = false;
            int cross_size =
                -1; // Количество невыполненных клоз в остальных кроме cross
                    // подстановках (не считая клоз, которые полностью не выполнены)

            int cross_row = -1;

            if (partition_size >= 2)
            {
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
                            // На месте cross стоит не ?, а NO. В таком случае мы не можем
                            // применить cross_reduce
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
                    // Если можно выполнить cross_reduce, то все остальные подстановки -
                    // одинаковые
                    cross_reduce = true;

                    for (int cl = 0; cl < (int)this->clauses.size(); ++cl) // Перебираем все клозы
                    {
                        char clause_result = '#'; // не инициализированное значение клозы

                        for (int i = 0; i < rcnt; ++i) // Пробегаем по всем подстановкам из
                                                       // нашего разбиения без cross_row
                        {
                            if (cs[i] != c || i == cross_row)
                            {
                                continue;
                            }

                            if (((rclauses[cross_row] >> cl) & 1) !=
                                ((rclauses[i] >> cl) & 1))
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

            vector<int> best_extra_branch;
            double best_extra_factor = C;

            // Переменные для трекинга лемм
            string best_extra_rule = "";
            int best_lemma_var_id = -1;
            int best_lemma_local_D = -1;
            int best_lemma_pos = -1;
            int best_lemma_neg = -1;

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
                            if (l->id != UNKNOWN_LITERAL.id &&
                                l->id != UNKNOWN_NOT_EMPTY_LITERAL.id)
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
                    if (pos + neg == 3 &&
                        ((pos == 2 && neg == 1) || (pos == 1 && neg == 2)))
                    {
                        lemma3_singletons_cnt++;
                    }
                }

                for (auto const &[id, counts] : var_counts)
                {
                    int pos = counts.first;
                    int neg = counts.second;

                    // ---------- Лемма 3 ----------
                    if (pos + neg == 3 &&
                        ((pos == 2 && neg == 1) || (pos == 1 && neg == 2)))
                    {
                        bool need_inv = (pos == 1 ? false : true);
                        int local_D = 0;
                        bool found_clause = false;

                        for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                        {
                            if (((gclauses >> cl) & 1) == 0 &&
                                ((gnoclauses >> cl) & 1) == 0)
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

                        if (found_clause)
                        {
                            vector<int> cand;
                            string cand_rule;

                            if (lemma3_singletons_cnt >= 2)
                            {
                                cand = {2, 9, 8};
                                cand_rule = "double_lemma3";
                            }
                            else
                            {
                                cand = {1, max(8, 7 + 2 * local_D)};
                                cand_rule = "lemma3";
                            }

                            double cand_factor = branching_factor(cand);

                            if (cand_factor < best_extra_factor)
                            {
                                best_extra_factor = cand_factor;
                                best_extra_branch = cand;
                                best_extra_rule = cand_rule;
                                best_lemma_var_id = id;
                                best_lemma_local_D = local_D;
                                best_lemma_pos = pos;
                                best_lemma_neg = neg;
                            }
                        }
                    }

                    // ---------- Лемма 2 ----------
                    if (pos > 0 && neg > 0 && (pos == 1 || neg == 1))
                    {
                        bool minority_inv =
                            (neg ==
                             1); // unique opposite clause contains ~x if neg==1, else x
                        int local_i = max(pos, neg);
                        int local_D = -1;

                        for (int cl = 0; cl < (int)this->clauses.size(); ++cl)
                        {
                            if (((gclauses >> cl) & 1) == 0 &&
                                ((gnoclauses >> cl) & 1) == 0)
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
                                best_extra_rule = "lemma2";
                                best_lemma_var_id = id;
                                best_lemma_local_D = local_D;
                                best_lemma_pos = pos;
                                best_lemma_neg = neg;
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

                int basic_reduce =
                    count_set_bits(gclauses) + count_set_bits(gnoclauses);

                GroupWitness gw;
                gw.basic_reduce_val = basic_reduce;

                if (cross_reduce && cross_size <= 2)
                {
                    if (cross_size == 1)
                        now_branch.push_back(basic_reduce + 1);
                    else
                    {
                        now_branch.push_back(basic_reduce + 1);
                        now_branch.push_back(basic_reduce + 8);
                    }

                    gw.rule = "cross_reduce";
                    gw.cross_row_idx = cross_row;
                    gw.cross_size = cross_size;
                }
                else if (!best_extra_branch.empty())
                {
                    for (int x : best_extra_branch)
                    {
                        now_branch.push_back(basic_reduce + x);
                    }

                    gw.rule = best_extra_rule;
                    gw.lemma_var_id = best_lemma_var_id;
                    gw.lemma_local_D = best_lemma_local_D;
                    gw.lemma_pos_count = best_lemma_pos;
                    gw.lemma_neg_count = best_lemma_neg;
                }
                else
                {
                    now_branch.push_back(basic_reduce);
                    gw.rule = "basic";
                }

                now_witnesses.push_back(gw);
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
            mn_witnesses = now_witnesses;
        }

    } while (is_3_case ? get_next_3_partition_fast(cs, mask_of_reduced_subsets)
                       : get_next_partition(cs, max_partitions));

    if (mn_branch.empty())
        return ProofNode({0});

    ProofNode node;
    node.type = "leaf";
    node.vec = mn_branch;
    node.tau = mn_factor;

    // node.partition = mn_partition;

    vector<int> full_partition(1 << k, -1);
    for (int i = 0; i < rcnt; ++i)
    {
        full_partition[masks[i]] = mn_partition[i];
    }
    node.partition = full_partition;

    node.formula_snapshot = this->get_snapshot();
    node.subsumptions = current_subsumptions;
    node.group_witnesses = mn_witnesses;

    return node;
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
            throw runtime_error("Cannot bracket root: high grew too large. Branch: " +
                                v_str);
        }
    }

    double fl = f(low);
    double fh = f(high);
    if (!(fl > 0.0 && fh < 0.0))
    {
        // numerical safeguard: if fl already <= 0 (rare), move low slightly toward
        // 1
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
                throw runtime_error("Failed to bracket root (fl, fh) = (" +
                                    to_string(fl) + ", " + to_string(fh) + ") " +
                                    v_str);
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

unordered_map<string, long long> *used_nodes;

void preprocess(int maximum_clause_size)
{
    used_nodes = new unordered_map<string, long long>();
    ID2VAR[0] = "?";
    VAR2ID["?"] = 0;
    ID2VAR[1] = "?+";
    VAR2ID["?+"] = 1;

    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = maximum_clause_size;

    POSSIBLE_LITERALS = {{1, 3, SINGLETON}, {3, 1, SINGLETON}, {2, 2, ANY}, {3, 2, ANY}, {2, 3, ANY}, {1, 4, SINGLETON}, {4, 1, SINGLETON}};

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
                lits_str.push_back((lit->inv ? "~" : "=") +
                                   to_string(lit->id == 0 ? 0 : perm[lit->id - 1]));
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

    return max_str;
}

vector<CNF *> add_new_var_universal(CNF *cnf, string v_name, int i, int j,
                                    LitType type, int pos,
                                    bool only_pos, bool silent,
                                    vector<long long> &out_children_ids)
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
            for (int a = max(0, s - j); a <= min(i, s); ++a)
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
                            if (now_cnf->clauses[k]->lits.find(&UNKNOWN_LITERAL) !=
                                    now_cnf->clauses[k]->lits.end() ||
                                now_cnf->clauses[k]->lits.find(&UNKNOWN_NOT_EMPTY_LITERAL) !=
                                    now_cnf->clauses[k]->lits.end())
                            {

                                if (now_cnf->clauses[k]->lits.find(
                                        &UNKNOWN_NOT_EMPTY_LITERAL) !=
                                    now_cnf->clauses[k]->lits.end())
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
                            vector<Literal *> new_clause_list = {new_lit_neg,
                                                                 &UNKNOWN_LITERAL};
                            Clause *new_clause_x = new Clause(new_clause_list);
                            now_cnf->clauses.push_back(new_clause_x);
                        }
                    }

                    if (MaxSATSettings.MAXIMUM_CLAUSE_SIZE != -1)
                    {
                        bool too_many_lits = false;

                        for (Clause *c : now_cnf->clauses)
                        {
                            if (c->lits.size() > MaxSATSettings.MAXIMUM_CLAUSE_SIZE + 1 ||
                                (c->lits.size() == MaxSATSettings.MAXIMUM_CLAUSE_SIZE + 1 &&
                                 c->lits.find(&UNKNOWN_LITERAL) == c->lits.end()))
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

                    if (used_nodes->find(now_cnf_str) == used_nodes->end())
                    {
                        ans.push_back(now_cnf);
                        (*used_nodes)[now_cnf_str] = now_cnf->node_id;
                        out_children_ids.push_back(now_cnf->node_id); // Сохраняем ID нового графа
                    }
                    else
                    {
                        // Граф изоморфен! Линкуем родителя со старым узлом, чтобы не рвать топологию
                        out_children_ids.push_back((*used_nodes)[now_cnf_str]);
                        delete now_cnf; // Заодно чиним утечку памяти
                    }

                    // ans.push_back(now_cnf);

                } while (prev_permutation(xm.begin(), xm.end()));
            }

        } while (prev_permutation(m.begin(), m.end()));
    }

    if (!silent)
    {
        vector<long long> unique_children_ids;
        unordered_set<long long> seen;
        for (long long id : out_children_ids) {
            if (seen.insert(id).second) {
                unique_children_ids.push_back(id);
            }
        }
        global_logger.log_add_variable(cnf->node_id, cnf->get_snapshot(), VAR2ID[v_name], i, j, unique_children_ids);
    }

    return ans;
}

vector<CNF *> add_new_var(CNF *cnf, string v_name, int i, int j, LitType type)
{
    vector<long long> dummy_ids;
    return add_new_var_universal(cnf, v_name, i, j, type, -1, false, false, dummy_ids);
}

vector<CNF *>
add_new_var_in_place(CNF *cnf, string v_name,
                     const std::function<int(CNF *)> &need_index_func,
                     vector<LiteralDegType> variants)
{
    int pos = need_index_func(cnf);

    vector<CNF *> ans;

    vector<long long> all_children_ids;
    
    for (LiteralDegType l : variants) {
        auto new_vars = add_new_var_universal(cnf, v_name, l.i, l.j, l.type, pos, true, true, all_children_ids);
        ans.insert(ans.end(), new_vars.begin(), new_vars.end());
    }

    CNF *cnf_empty_space = new CNF(*cnf);

    if (pos < cnf_empty_space->clauses.size() &&
        cnf_empty_space->clauses[pos]->lits.find(&UNKNOWN_LITERAL) !=
            cnf_empty_space->clauses[pos]->lits.end())
    {
        cnf_empty_space->clauses[pos]->lits.erase(&UNKNOWN_LITERAL);
    }

    if (cnf_empty_space->clauses.size() != 0) {
        ans.push_back(cnf_empty_space);
        all_children_ids.push_back(cnf_empty_space->node_id);
    }

    vector<long long> unique_children_ids;
    unordered_set<long long> seen;
    for (long long id : all_children_ids) {
        if (seen.insert(id).second) {
            unique_children_ids.push_back(id);
        }
    }

    global_logger.log_addpos(cnf->node_id, cnf->get_snapshot(), VAR2ID[v_name], pos, unique_children_ids);

    return ans;
}

// Функция возвращает пару {CNF_с_пустотой, CNF_с_непустотой(?+)}
DivideResult empty_divide(CNF *cnf)
{
    DivideResult best_split;
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
            // 1. Создаем ветку, где '?' означает пустоту (удаляем '?')
            CNF *cnf_empty = new CNF(*cnf);
            cnf_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);

            // 2. Создаем ветку, где '?' означает минимум 1 литерал (заменяем на '?+')
            CNF *cnf_not_empty = new CNF(*cnf);
            cnf_not_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);
            cnf_not_empty->clauses[i]->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);

            // Оцениваем обе ветки. Теперь xiao_branch и branch_group возвращают ProofNode
            ProofNode empty_xiao = cnf_empty->xiao_branch(1, "x");
            ProofNode empty_group = cnf_empty->branch_group(ids);
            ProofNode best_empty = (empty_xiao.tau < empty_group.tau) ? empty_xiao : empty_group;

            ProofNode not_empty_xiao = cnf_not_empty->xiao_branch(1, "x");
            ProofNode not_empty_group = cnf_not_empty->branch_group(ids);
            ProofNode best_not_empty = (not_empty_xiao.tau < not_empty_group.tau) ? not_empty_xiao : not_empty_group;

            // Худший случай при данном разбиении
            double worst_factor = max(best_empty.tau, best_not_empty.tau);

            if (worst_factor < min_worst_factor)
            {
                min_worst_factor = worst_factor;

                // Очищаем предыдущий лучший вариант
                if (best_split.cnf_empty)
                    delete best_split.cnf_empty;
                if (best_split.cnf_not_empty)
                    delete best_split.cnf_not_empty;

                best_split.clause_idx = i;
                best_split.cnf_empty = cnf_empty;
                best_split.cnf_not_empty = cnf_not_empty;

                // СВЯЗЫВАЕМ СЕРТИФИКАТЫ ОБЩИМ ПРЕДКОМ
                best_split.proof_tree.type = "divide_clause";
                best_split.proof_tree.target_clause_idx = i;
                best_split.proof_tree.tau = worst_factor;
                best_split.proof_tree.formula_snapshot = cnf->get_snapshot();
                best_split.proof_tree.children = {best_empty, best_not_empty};
            }
            else
            {
                // Если вариант не лучше, сразу удаляем созданные копии
                delete cnf_empty;
                delete cnf_not_empty;
            }
        }
    }

    global_logger.log_divide(cnf->node_id, cnf->get_snapshot(), best_split.proof_tree.target_clause_idx, best_split.cnf_empty->node_id, best_split.cnf_not_empty->node_id);

    return best_split;
}