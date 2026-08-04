#include "cnf.h"
#include "cert_logger.h"

#include <algorithm>
#include <assert.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <math.h>
#include <set>
#include <string>
#include <unordered_set>

// #include <fstream>

using namespace std;

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 2;
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

// Residual formulas are short-lived and may be materialized hundreds of
// thousands of times.  Reuse immutable literal objects instead of allocating
// a fresh Literal for every occurrence in every candidate grouping.
Literal *intern_literal(int id, bool inv)
{
    static map<pair<int, bool>, unique_ptr<Literal>> pool;
    pair<int, bool> key = {id, inv};
    auto it = pool.find(key);
    if (it == pool.end())
        it = pool.emplace(key, make_unique<Literal>(id, inv)).first;
    return it->second.get();
}

long long GLOBAL_NODE_ID_COUNTER = 0;
int GLOBAL_TAIL_ATOM_COUNTER = 0;

int fresh_tail_atom() { return ++GLOBAL_TAIL_ATOM_COUNTER; }

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

std::vector<std::vector<int>> CNF::get_cert_snapshot()
{
    std::vector<std::vector<int>> snap;
    for (Clause *c : clauses)
    {
        std::vector<int> cl_snap;
        for (Literal *l : c->lits)
            if (!is_any_unknown_literal(l))
                cl_snap.push_back((l->inv ? -1 : 1) * l->id);
        for (auto const &[tail_id, nonempty] : c->tail_atoms)
            cl_snap.push_back((nonempty ? SNAP_TAIL_NONEMPTY_BASE
                                        : SNAP_TAIL_ANY_BASE) + tail_id);
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
    node.formula_snapshot = this->get_cert_snapshot();
    node.subsumptions = current_subsumptions;

    vector<int> full_partition(1 << k, -1);
    for (int i = 0; i < (int)branch.size(); ++i)
    {
        full_partition[valid_masks[i]] = i;
    }
    node.partition = full_partition;
    node.type = "enumeration";
    node.branch_ids = ids;

    map<int, int> id_to_index;
    for (int i = 0; i < k; ++i) id_to_index[ids[i]] = i;
    for (int mask : valid_masks)
    {
        vector<vector<int>> residual;
        int offset = 0;
        int decrease = 0;
        for (Clause *clause : clauses)
        {
            bool satisfied = false;
            vector<int> child_clause;
            for (Literal *lit : clause->lits)
            {
                if (is_any_unknown_literal(lit)) continue;
                auto it = id_to_index.find(lit->id);
                if (it == id_to_index.end())
                    child_clause.push_back((lit->inv ? -1 : 1) * lit->id);
                else
                {
                    bool value = ((mask >> it->second) & 1) != 0;
                    if (value != lit->inv) satisfied = true;
                }
            }
            if (satisfied)
            {
                ++offset;
                ++decrease;
                continue;
            }
            for (auto const &[tail_id, nonempty] : clause->tail_atoms)
                child_clause.push_back((nonempty ? SNAP_TAIL_NONEMPTY_BASE
                                                 : SNAP_TAIL_ANY_BASE) + tail_id);
            if (child_clause.empty())
            {
                ++decrease;
                continue;
            }
            residual.push_back(move(child_clause));
        }

        ProofNode call({0});
        call.tau = 100.0;
        call.formula_snapshot = residual;
        ProofAlternative alternative;
        alternative.offset = offset;
        alternative.decrease = decrease;
        alternative.assignments = {mask};
        alternative.represented_masks = {mask};
        alternative.proof = make_shared<ProofNode>(move(call));
        node.alternatives.push_back(move(alternative));
    }

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

bool is_any_unknown_literal(const Literal *l)
{
    return l == &UNKNOWN_LITERAL || l == &UNKNOWN_NOT_EMPTY_LITERAL;
}

map<int, FormulaVarStats> analyze_formula(const CNF &cnf)
{
    map<int, FormulaVarStats> stats;

    for (int clause_idx = 0; clause_idx < (int)cnf.clauses.size(); ++clause_idx)
    {
        Clause *clause = cnf.clauses[clause_idx];
        set<int> named_ids;
        int named_literal_count = 0;
        bool has_unknown = false;
        bool has_not_empty = false;

        for (Literal *lit : clause->lits)
        {
            if (lit == &UNKNOWN_LITERAL)
            {
                has_unknown = true;
                continue;
            }
            if (lit == &UNKNOWN_NOT_EMPTY_LITERAL)
            {
                has_not_empty = true;
                continue;
            }
            named_ids.insert(lit->id);
            named_literal_count++;
            stats[lit->id];
        }

        bool is_unit = !has_unknown && !has_not_empty && named_literal_count == 1;

        for (Literal *lit : clause->lits)
        {
            if (is_any_unknown_literal(lit))
                continue;

            FormulaVarStats &st = stats[lit->id];
            int local_D = (int)named_ids.size() - 1 + (has_not_empty ? 1 : 0);
            if (lit->inv)
            {
                st.neg_count++;
                st.neg_indices.push_back(clause_idx);
                st.neg_min_D = min(st.neg_min_D, local_D);
                if (is_unit) st.neg_unit_count++;
            }
            else
            {
                st.pos_count++;
                st.pos_indices.push_back(clause_idx);
                st.pos_min_D = min(st.pos_min_D, local_D);
                if (is_unit) st.pos_unit_count++;
            }
        }
    }

    return stats;
}

void destroy_cnf(CNF *cnf)
{
    if (!cnf) return;
    for (Clause *clause : cnf->clauses)
        delete clause;
    delete cnf;
}

GroupResidual materialize_group_residual(const CNF &cnf,
                                         const vector<int> &ids,
                                         const vector<int> &group_masks)
{
    GroupResidual result;
    int k = (int)ids.size();
    int group_size = (int)group_masks.size();

    if (group_size == 0 || (group_size & (group_size - 1)) != 0)
    {
        result.error = "group size is not a positive power of two";
        return result;
    }
    if (group_size >= 31 || cnf.clauses.size() >= 31)
    {
        result.error = "group residual currently requires masks narrower than 31 bits";
        return result;
    }

    set<int> unique_masks(group_masks.begin(), group_masks.end());
    if ((int)unique_masks.size() != group_size)
    {
        result.error = "group contains duplicate assignments";
        return result;
    }

    map<int, int> id_to_index;
    for (int j = 0; j < k; ++j)
        id_to_index[ids[j]] = j;

    vector<int> columns(k, 0);
    for (int j = 0; j < k; ++j)
        for (int row = 0; row < group_size; ++row)
            if ((group_masks[row] >> j) & 1)
                columns[j] |= (1 << row);

    int all_ones = (1 << group_size) - 1;
    vector<int> repr_id(k, -1);
    vector<bool> repr_inv(k, false);
    int free_variables = 0;

    for (int j = 0; j < k; ++j)
    {
        if (columns[j] == 0 || columns[j] == all_ones)
        {
            // For fixed variables, the bool stores the fixed truth value.
            result.representative_map[ids[j]] = {-1, columns[j] == all_ones};
            continue;
        }

        if (count_set_bits(columns[j]) * 2 != group_size)
        {
            result.error = "a non-constant group column is not balanced";
            return result;
        }

        bool found = false;
        for (int previous = 0; previous < j; ++previous)
        {
            if (repr_id[previous] == -1)
                continue;

            int representative_column = columns[previous];
            if (repr_inv[previous])
                representative_column = (~representative_column) & all_ones;

            if (columns[j] == representative_column)
            {
                repr_id[j] = repr_id[previous];
                repr_inv[j] = false;
                found = true;
                break;
            }
            if (columns[j] == ((~representative_column) & all_ones))
            {
                repr_id[j] = repr_id[previous];
                repr_inv[j] = true;
                found = true;
                break;
            }
        }

        if (!found)
        {
            repr_id[j] = ids[j];
            repr_inv[j] = false;
            free_variables++;
        }
        result.representative_map[ids[j]] = {repr_id[j], repr_inv[j]};
    }

    if (group_size != (1 << free_variables))
    {
        result.error = "group is not representable by constants and signed representatives";
        return result;
    }

    int common_satisfied = 0;
    int common_empty = 0;
    for (int clause_idx = 0; clause_idx < (int)cnf.clauses.size(); ++clause_idx)
    {
        Clause *clause = cnf.clauses[clause_idx];
        bool satisfied_in_all_rows = true;
        bool empty_in_all_rows = true;

        for (int row_mask : group_masks)
        {
            bool satisfied = false;
            bool has_unassigned_literal = false;
            for (Literal *lit : clause->lits)
            {
                auto branch_it = id_to_index.find(lit->id);
                if (branch_it == id_to_index.end())
                {
                    has_unassigned_literal = true;
                    continue;
                }

                bool value = ((row_mask >> branch_it->second) & 1) != 0;
                if (value != lit->inv)
                {
                    satisfied = true;
                    break;
                }
            }
            satisfied_in_all_rows = satisfied_in_all_rows && satisfied;
            empty_in_all_rows = empty_in_all_rows && !satisfied && !has_unassigned_literal;
        }

        if (satisfied_in_all_rows)
            common_satisfied |= (1 << clause_idx);
        if (empty_in_all_rows)
            common_empty |= (1 << clause_idx);
    }

    result.common_satisfied_mask = common_satisfied;
    result.common_empty_mask = common_empty;
    result.base_decrease = count_set_bits(common_satisfied) + count_set_bits(common_empty);
    result.cnf = new CNF();

    for (int clause_idx = 0; clause_idx < (int)cnf.clauses.size(); ++clause_idx)
    {
        if (((common_satisfied | common_empty) >> clause_idx) & 1)
            continue;

        vector<Literal *> transformed;
        map<int, int> polarity_mask;
        bool became_satisfied = false;

        for (Literal *lit : cnf.clauses[clause_idx]->lits)
        {
            if (is_any_unknown_literal(lit))
            {
                transformed.push_back(lit);
                continue;
            }

            auto image_it = result.representative_map.find(lit->id);
            if (image_it == result.representative_map.end())
            {
                transformed.push_back(lit);
                polarity_mask[lit->id] |= lit->inv ? 2 : 1;
                continue;
            }

            int image_id = image_it->second.first;
            bool image_flag = image_it->second.second;
            if (image_id == -1)
            {
                bool literal_value = image_flag != lit->inv;
                if (literal_value)
                {
                    became_satisfied = true;
                    break;
                }
                continue;
            }

            bool image_inv = lit->inv ^ image_flag;
            transformed.push_back(intern_literal(image_id, image_inv));
            polarity_mask[image_id] |= image_inv ? 2 : 1;
        }

        bool tautology = false;
        for (auto const &[id, polarities] : polarity_mask)
            if (polarities == 3)
                tautology = true;

        if (became_satisfied || tautology || transformed.empty())
        {
            result.error = "materialization found an unaccounted common clause";
            destroy_cnf(result.cnf);
            result.cnf = nullptr;
            return result;
        }

        result.cnf->clauses.push_back(
            new Clause(transformed, cnf.clauses[clause_idx]->tail_atoms));
    }

    result.valid = true;
    return result;
}

// Проверяет корректность одной группы подстановок для k переменных ветвления.
//
// group_masks — набор масок (каждая маска — k-битное число, бит j = значение ids[j]).
// k           — число переменных ветвления.
// diag        — выходная строка с диагностикой при ошибке.
//
// Возвращает true, если группа корректна.
bool check_group_validity(const vector<int>& group_masks, int k, string& diag)
{
    int gsz = (int)group_masks.size();

    if (gsz == 0)
    {
        diag = "Пустая группа";
        return false;
    }

    // Быстрая проверка: размер должен быть степенью двойки
    if ((gsz & (gsz - 1)) != 0)
    {
        diag = "Размер группы (" + to_string(gsz) + ") не является степенью двойки";
        return false;
    }

    int all_ones = (1 << gsz) - 1;

    // Вычисляем столбики: column[j] — битмаска значений переменной j
    vector<int> column(k, 0);
    for (int j = 0; j < k; ++j)
        for (int s = 0; s < gsz; ++s)
            if ((group_masks[s] >> j) & 1)
                column[j] |= (1 << s);

    // Классифицируем переменные и ищем представителей
    vector<int>  repr_id(k, -1);   // -1 = константа
    vector<bool> repr_inv(k, false);
    int num_free_vars = 0;

    for (int j = 0; j < k; ++j)
    {
        if (column[j] == 0 || column[j] == all_ones)
            continue; // константа

        // Проверка баланса
        int ones = count_set_bits(column[j]);
        if (ones * 2 != gsz)
        {
            diag = "Переменная " + to_string(j) + " (столбик 0b";
            for (int s = gsz - 1; s >= 0; --s)
                diag += ((column[j] >> s) & 1) ? "1" : "0";
            diag += ") имеет " + to_string(ones) + " единиц из " +
                    to_string(gsz) + " (требуется ровно " + to_string(gsz / 2) + ")";
            return false;
        }

        // Ищем представителя среди j' < j
        bool found_repr = false;
        for (int jp = 0; jp < j; ++jp)
        {
            if (repr_id[jp] == -1)
                continue; // jp — константа

            int base_col = column[jp];
            if (repr_inv[jp])
                base_col = (~base_col) & all_ones;

            if (base_col == column[j])
            {
                repr_id[j]  = repr_id[jp];
                repr_inv[j] = false;
                found_repr  = true;
                break;
            }
            if ((~base_col & all_ones) == column[j])
            {
                repr_id[j]  = repr_id[jp];
                repr_inv[j] = true;
                found_repr  = true;
                break;
            }
        }

        if (!found_repr)
        {
            repr_id[j]  = j; // используем индекс как id представителя
            repr_inv[j] = false;
            num_free_vars++;
        }
    }

    // Финальная проверка: partition_size == 2^num_free_vars
    if (gsz != (1 << num_free_vars))
    {
        diag = "partition_size=" + to_string(gsz) +
               " != 2^num_free_vars=2^" + to_string(num_free_vars) +
               "=" + to_string(1 << num_free_vars) +
               ". Столбики переменных: [";
        for (int j = 0; j < k; ++j)
        {
            diag += "var" + to_string(j) + "=0b";
            for (int s = gsz - 1; s >= 0; --s)
                diag += ((column[j] >> s) & 1) ? "1" : "0";
            if (j + 1 < k) diag += ", ";
        }
        diag += "]";
        return false;
    }

    return true;
}

ProofNode CNF::branch_group(vector<int> ids, int max_partitions,
                            bool construct_proof)
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

    vector<GroupWitness> mn_witnesses;

    struct GroupCombination
    {
        vector<int> vec;
        vector<GroupWitness> witnesses;
    };

    struct ResidualSearchSummary
    {
        int decrease = 0;
        vector<int> vec;
        vector<string> rules;
        vector<vector<int>> formula;
        double factor = 100.0;
        string rule;
    };
    map<unsigned long long, ResidualSearchSummary> residual_search_cache;

    do
    {
        bool got_zero = false;
        bool no_merge_config = false;
        vector<GroupCombination> combinations(1);

        int max_class = -1;

        for (int i = 0; i < rcnt; ++i)
        {
            if (cs[i] > max_class)
                max_class = cs[i];
        }

        for (int c = 0; c <= max_class; ++c)
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

            // -------------------------------------------------------
            // Материализация остаточной формулы группы.
            //
            // Каждая переменная ветвления заменяется
            // либо на константу 0/1, либо на одну из новых свободных
            // переменных (возможно с отрицанием). Группа корректна
            // Все проверки корректности отображения выполняются внутри
            // materialize_group_residual.
            // -------------------------------------------------------

            // Собираем маски подстановок текущего класса c
            vector<int> group_subst_masks;
            for (int i = 0; i < rcnt; ++i)
                if (cs[i] == c)
                    group_subst_masks.push_back(masks[i]);

            GroupResidual group_residual =
                materialize_group_residual(*this, ids, group_subst_masks);
            if (!group_residual.valid ||
                group_residual.common_satisfied_mask != gclauses ||
                group_residual.common_empty_mask != gnoclauses)
            {
                if (group_residual.cnf)
                    destroy_cnf(group_residual.cnf);
                no_merge_config = true;
                break;
            }
            unique_ptr<CNF, void (*)(CNF *)> residual_guard(group_residual.cnf,
                                                            destroy_cnf);

            vector<pair<vector<int>, GroupWitness>> extra_choices;

            if (partition_size >= 2)
            {
                // -------------------------------------------------------
                // Единая фаза подсчёта статистики по repr-переменным.
                //
                // Для каждого представителя (rid) и каждой полярности
                // считаем:
                //   count     — число клоз с вхождением (с дедупликацией)
                //   unit_count — из них: unit-клозы (только этот repr, без ? и ?+)
                //   min_D     — мин. количество ДРУГИХ repr-переменных в клозе
                //
                // Подсчёт ведётся по клозам (не по литералам!), чтобы
                // корректно обрабатывать случай когда несколько исходных
                // переменных ветвления склеились в одного представителя.
                // -------------------------------------------------------

                map<int, FormulaVarStats> repr_stats =
                    analyze_formula(*group_residual.cnf);

                // -------------------------------------------------------
                // Применение лемм на основе precomputed repr_stats
                // -------------------------------------------------------

                for (const DirectLemmaResult &direct_lemma :
                     find_direct_lemma23_candidates(*group_residual.cnf))
                {
                    GroupWitness witness;
                    witness.rule = direct_lemma.rule;
                    witness.lemma_var_id = direct_lemma.pivot_id;
                    witness.second_lemma_var_id = direct_lemma.second_pivot_id;
                    witness.lemma_local_D = direct_lemma.local_D;
                    witness.lemma_pos_count = direct_lemma.pos_count;
                    witness.lemma_neg_count = direct_lemma.neg_count;
                    witness.claimed_vector = direct_lemma.vec;
                    extra_choices.push_back({direct_lemma.vec, witness});
                }

                for (auto const &[id, st] : repr_stats)
                {
                    int pos = st.pos_count;
                    int neg = st.neg_count;

                    // ---------- Лемма 4 ----------
                    // Условие: i >= j >= 2.
                    // Если хотя бы (j-1) клоз с самим (i,j)-литералом
                    // являются unit-клозами, вектор ветвления >= (i, 2j+1).
                    if (pos >= 2 && neg >= 2)
                    {
                        // Пробуем оба направления
                        for (int try_dir = 0; try_dir < 2; ++try_dir)
                        {
                            int local_j    = (try_dir == 0) ? neg : pos;
                            int local_i4   = (try_dir == 0) ? pos : neg;
                            int unit_count = (try_dir == 0) ? st.pos_unit_count : st.neg_unit_count;

                            if (local_i4 < local_j) continue; // нужно i >= j

                            if (unit_count >= local_j - 1)
                            {
                                GroupWitness witness;
                                witness.rule = "lemma4";
                                witness.lemma_var_id = id;
                                witness.lemma_local_D = local_j;
                                witness.lemma_pos_count = pos;
                                witness.lemma_neg_count = neg;
                                witness.claimed_vector = {local_i4, 2 * local_j + 1};
                                extra_choices.push_back(
                                    {{local_i4, 2 * local_j + 1}, witness});
                            }
                        }
                    }
                }
            }

            // Run the constructive reductions on the actual residual CNF.
            // If no reduction applies, use the cheap non-group Xiao search as
            // an additional candidate for this affine class.
            unsigned long long residual_key = 0;
            bool cacheable_residual = true;
            for (int assignment_mask : group_subst_masks)
            {
                if (assignment_mask < 0 || assignment_mask >= 64)
                {
                    cacheable_residual = false;
                    break;
                }
                residual_key |= 1ULL << assignment_mask;
            }

            ResidualSearchSummary residual_summary;
            auto cached_residual = cacheable_residual
                                     ? residual_search_cache.find(residual_key)
                                     : residual_search_cache.end();
            if (cached_residual != residual_search_cache.end())
            {
                residual_summary = cached_residual->second;
            }
            else
            {
                ReductionFixpoint reduced_residual =
                    reduce_to_fixpoint(*group_residual.cnf);
                unique_ptr<CNF, void (*)(CNF *)> reduced_residual_guard(
                    reduced_residual.cnf, destroy_cnf);

                residual_summary.formula = group_residual.cnf->get_cert_snapshot();
                if (reduced_residual.total_decrease > 0)
                {
                    residual_summary.decrease = reduced_residual.total_decrease;
                    residual_summary.vec = {reduced_residual.total_decrease};
                    residual_summary.factor = branching_factor(residual_summary.vec);
                    residual_summary.rule = "residual_rr";
                    for (const ReductionStep &step : reduced_residual.steps)
                        residual_summary.rules.push_back(step.rule);
                }
                else
                {
                    ProofNode fast_residual =
                        reduced_residual.cnf->xiao_branch(1, "");
                    residual_summary.vec = fast_residual.vec;
                    residual_summary.factor = fast_residual.tau;
                    residual_summary.rule = "residual_xiao";
                }

                if (cacheable_residual)
                    residual_search_cache[residual_key] = residual_summary;
            }

            bool residual_has_progress = false;
            for (int value : residual_summary.vec)
                residual_has_progress |= value > 0;
            if (residual_has_progress)
            {
                GroupWitness witness;
                witness.rule = residual_summary.rule;
                witness.residual_decrease = residual_summary.decrease;
                witness.residual_vector = residual_summary.vec;
                witness.residual_formula = residual_summary.formula;
                    witness.residual_reduction_rules = residual_summary.rules;
                witness.claimed_vector = residual_summary.vec;
                extra_choices.push_back({residual_summary.vec, witness});
            }

            if (has_class)
            {
                int basic_reduce =
                    count_set_bits(gclauses) + count_set_bits(gnoclauses);
                if (basic_reduce != group_residual.base_decrease)
                {
                    no_merge_config = true;
                    break;
                }

                vector<pair<vector<int>, GroupWitness>> class_choices;

                if (basic_reduce > 0)
                {
                    GroupWitness witness;
                    witness.rule = "basic";
                    witness.basic_reduce_val = basic_reduce;
                    class_choices.push_back({{basic_reduce}, witness});
                }

                for (auto choice : extra_choices)
                {
                    for (int &value : choice.first)
                        value += basic_reduce;
                    choice.second.basic_reduce_val = basic_reduce;
                    class_choices.push_back(move(choice));
                }

                if (class_choices.empty())
                {
                    got_zero = true;
                    break;
                }

                vector<GroupCombination> next_combinations;
                set<vector<int>> seen_vectors;
                for (const GroupCombination &partial : combinations)
                {
                    for (const auto &choice : class_choices)
                    {
                        GroupCombination next = partial;
                        next.vec.insert(next.vec.end(), choice.first.begin(),
                                        choice.first.end());
                        next.witnesses.push_back(choice.second);
                        vector<int> key = next.vec;
                        sort(key.begin(), key.end(), greater<int>());
                        if (seen_vectors.insert(key).second)
                            next_combinations.push_back(move(next));
                    }
                }
                combinations.swap(next_combinations);
            }
        }

        if (got_zero || no_merge_config)
        {
            continue;
        }

        for (const GroupCombination &combination : combinations)
        {
            double now_factor = branching_factor(combination.vec);
            if (now_factor < mn_factor)
            {
                mn_factor = now_factor;
                mn_branch = combination.vec;
                mn_partition = cs;
                mn_witnesses = combination.witnesses;
            }
        }

    } while (is_3_case ? get_next_3_partition_fast(cs, mask_of_reduced_subsets)
                       : get_next_partition(cs, max_partitions));

    ProofNode direct_child_search = this->xiao_branch(1, "");
    if (mn_branch.empty())
        return direct_child_search;

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

    node.formula_snapshot = this->get_cert_snapshot();
    node.subsumptions = current_subsumptions;
    node.group_witnesses = mn_witnesses;

    // A split into the two affine classes v=0 and v=1 is exactly an ordinary
    // branch on v followed by analysis of both child CNFs.  Subsumption may
    // remove one row before the group enumerator sees that split, so retain
    // the cheap depth-1 Xiao search as a baseline candidate for branch_group.
    // This preserves the stronger subsumed partitions while recovering all
    // variable splits with the shared child lemmas.
    if (direct_child_search.tau < node.tau)
        return direct_child_search;

    if (!construct_proof)
        return node;

    node.type = "enumeration";
    node.branch_ids = ids;

    // Re-materialize only the winning partition.  Candidate residuals above
    // are intentionally short-lived; the certificate needs constructive
    // children only for the selected proof.
    int winning_max_class = -1;
    for (int value : mn_partition) winning_max_class = max(winning_max_class, value);
    size_t winning_witness_index = 0;
    for (int c = 0; c <= winning_max_class; ++c)
    {
        vector<int> group_masks;
        for (int i = 0; i < rcnt; ++i)
            if (mn_partition[i] == c) group_masks.push_back(masks[i]);
        if (group_masks.empty()) continue;

        GroupResidual residual = materialize_group_residual(*this, ids, group_masks);
        if (!residual.valid)
        {
            if (residual.cnf) destroy_cnf(residual.cnf);
            node.alternatives.clear();
            break;
        }

        if (winning_witness_index >= mn_witnesses.size())
        {
            destroy_cnf(residual.cnf);
            node.alternatives.clear();
            break;
        }
        const GroupWitness &witness = mn_witnesses[winning_witness_index++];
        ProofNode child;
        if (witness.rule == "basic")
        {
            child = ProofNode({0});
            child.tau = 100.0;
            child.formula_snapshot = residual.cnf->get_cert_snapshot();
        }
        else if (witness.rule == "residual_rr")
        {
            // Rebuild the exact reduction chain named by the winning search.
            CNF *current = new CNF(*residual.cnf);
            vector<ProofNode> parents;
            bool valid_chain = true;
            for (const string &rule : witness.residual_reduction_rules)
            {
                ReductionStep step = apply_named_reduction(*current, rule);
                if (!step.applied || !step.cnf)
                {
                    valid_chain = false;
                    if (step.cnf) destroy_cnf(step.cnf);
                    break;
                }
                ProofNode parent;
                parent.type = "reduction";
                parent.rule = rule;
                parent.pivot_id = step.pivot_id;
                parent.formula_snapshot = current->get_cert_snapshot();
                parent.rr_witness_clauses = step.witness_clauses;
                parents.push_back(move(parent));
                destroy_cnf(current);
                current = step.cnf;
            }
            child = ProofNode({0});
            child.tau = 100.0;
            child.formula_snapshot = current->get_cert_snapshot();
            if (valid_chain)
                for (auto it = parents.rbegin(); it != parents.rend(); ++it)
                {
                    it->children.push_back(move(child));
                    child = move(*it);
                }
            else
            {
                child.type = "leaf";
                child.rule = "residual_rr_reconstruction";
                child.vec = witness.claimed_vector;
                child.formula_snapshot = residual.cnf->get_cert_snapshot();
            }
            destroy_cnf(current);
        }
        else if (witness.rule == "residual_xiao")
        {
            child = residual.cnf->xiao_branch(1, "");
        }
        else
        {
            child.type = "leaf";
            child.rule = witness.rule;
            child.vec = witness.claimed_vector;
            child.tau = branching_factor(child.vec);
            child.formula_snapshot = residual.cnf->get_cert_snapshot();
        }

        ProofAlternative alternative;
        alternative.offset = count_set_bits(residual.common_satisfied_mask);
        alternative.decrease = residual.base_decrease;
        alternative.represented_masks = group_masks;
        alternative.proof = make_shared<ProofNode>(move(child));
        node.alternatives.push_back(move(alternative));
        destroy_cnf(residual.cnf);
    }

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
    // Only ordinary Boolean variables may be renamed.  IDs 0 and 1 are the
    // typed boundary symbols ? and ?+ and must remain fixed.
    vector<int> variables;
    for (Clause *clause : cnf->clauses)
        for (Literal *literal : clause->lits)
            if (literal->id >= 2)
                variables.push_back(literal->id);
    sort(variables.begin(), variables.end());
    variables.erase(unique(variables.begin(), variables.end()), variables.end());

    vector<int> perm(variables.size());
    for (int i = 0; i < (int)perm.size(); ++i)
        perm[i] = i + 2;

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
                int mapped_id = lit->id;
                if (lit->id >= 2)
                {
                    auto position = lower_bound(variables.begin(), variables.end(),
                                                lit->id);
                    mapped_id = perm[position - variables.begin()];
                }
                lits_str.push_back((lit->inv ? "~" : "=") +
                                   to_string(mapped_id));
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
                                    for (auto &[tail_id, nonempty] :
                                         now_cnf->clauses[k]->tail_atoms)
                                        nonempty = false;
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
                                c->tail_atoms.clear();
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
        global_logger.log_add_variable(cnf->node_id, cnf->get_cert_snapshot(), VAR2ID[v_name], i, j, unique_children_ids);
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
        cnf_empty_space->clauses[pos]->tail_atoms.clear();
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

    global_logger.log_addpos(cnf->node_id, cnf->get_cert_snapshot(), VAR2ID[v_name], pos, unique_children_ids);

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

    auto best_tau = [&](CNF *candidate)
    {
        double result;
        {
            ProofNode node = candidate->xiao_branch(1, "x");
            result = node.tau;
        }
        {
            ProofNode node = candidate->branch_group(ids);
            result = min(result, node.tau);
        }
        return result;
    };

    auto best_proof = [&](CNF *candidate)
    {
        double xiao_tau;
        {
            ProofNode node = candidate->xiao_branch(1, "x");
            xiao_tau = node.tau;
        }
        {
            ProofNode group_node = candidate->branch_group(ids);
            if (group_node.tau <= xiao_tau)
                return candidate->branch_group(ids, -1, true);
        }
        return candidate->xiao_branch(1, "x");
    };

    for (int i = 0; i < (int)cnf->clauses.size(); ++i)
    {
        Clause *c = cnf->clauses[i];

        // Ищем клозу, в которой есть обычный '?'
        if (c->lits.find(&UNKNOWN_LITERAL) != c->lits.end())
        {
            // 1. Создаем ветку, где '?' означает пустоту (удаляем '?')
            CNF *cnf_empty = new CNF(*cnf);
            cnf_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);
            cnf_empty->clauses[i]->tail_atoms.clear();

            // 2. Создаем ветку, где '?' означает минимум 1 литерал (заменяем на '?+')
            CNF *cnf_not_empty = new CNF(*cnf);
            cnf_not_empty->clauses[i]->lits.erase(&UNKNOWN_LITERAL);
            cnf_not_empty->clauses[i]->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);
            for (auto &[tail_id, nonempty] :
                 cnf_not_empty->clauses[i]->tail_atoms)
                nonempty = true;

            // Худший случай при данном разбиении
            double worst_factor = max(best_tau(cnf_empty),
                                      best_tau(cnf_not_empty));

            if (worst_factor < min_worst_factor)
            {
                min_worst_factor = worst_factor;

                // Очищаем предыдущий лучший вариант
                if (best_split.cnf_empty)
                    destroy_cnf(best_split.cnf_empty);
                if (best_split.cnf_not_empty)
                    destroy_cnf(best_split.cnf_not_empty);

                best_split.clause_idx = i;
                best_split.cnf_empty = cnf_empty;
                best_split.cnf_not_empty = cnf_not_empty;

            }
            else
            {
                // Если вариант не лучше, сразу удаляем созданные копии
                destroy_cnf(cnf_empty);
                destroy_cnf(cnf_not_empty);
            }
        }
    }

    if (best_split.cnf_empty && best_split.cnf_not_empty)
    {
        // Build the potentially large proof trees only once, for the split
        // which survived the numerical first pass.
        best_split.proof_tree.type = "divide_clause";
        best_split.proof_tree.target_clause_idx = best_split.clause_idx;
        best_split.proof_tree.formula_snapshot = cnf->get_cert_snapshot();
        best_split.proof_tree.children.push_back(
            best_proof(best_split.cnf_empty));
        best_split.proof_tree.children.push_back(
            best_proof(best_split.cnf_not_empty));
        best_split.proof_tree.tau = max(
            best_split.proof_tree.children[0].tau,
            best_split.proof_tree.children[1].tau);

        global_logger.log_divide(cnf->node_id, cnf->get_cert_snapshot(),
                                 best_split.proof_tree.target_clause_idx,
                                 best_split.cnf_empty->node_id,
                                 best_split.cnf_not_empty->node_id);
    }

    return best_split;
}
