#include "cnf.h"
#include "cert_logger.h"
#include "lemmas.h"
#include "strategy_cache.h"
#include "group_cover.h"

#include <algorithm>
#include <assert.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <memory>
#include <math.h>
#include <cmath>
#include <set>
#include <string>
#include <unordered_set>
#include <stdexcept>

// #include <fstream>

using namespace std;

MaxSATSettingsType MaxSATSettings{-1, true};

map<int, string> ID2VAR;
map<string, int> VAR2ID;
int ID_COUNTER = 2;
Literal UNKNOWN_LITERAL = Literal();
Literal UNKNOWN_NOT_EMPTY_LITERAL = Literal(1, false);

vector<LiteralDegType> POSSIBLE_LITERALS;

Literal::Literal() : id(0), inv(false) {};

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
void reserve_tail_atoms(int maximum_id) { GLOBAL_TAIL_ATOM_COUNTER = max(GLOBAL_TAIL_ATOM_COUNTER, maximum_id); }

CNF::CNF()
{
    node_id = ++GLOBAL_NODE_ID_COUNTER;
}

CNF::CNF(CNF &cnf)
{
    node_id = ++GLOBAL_NODE_ID_COUNTER;
    tail_exclusions = cnf.tail_exclusions;
    clauses.resize(cnf.clauses.size());
    for (int i = 0; i < (int)clauses.size(); ++i)
    {
        clauses[i] = new Clause(*cnf.clauses[i]);
    }
}

TailExclusions CNF::active_tail_exclusions() const
{
    TailExclusions result;
    if (tail_exclusions.empty()) return result;
    for (const auto *clause : clauses)
        for (const auto &[tail, flag] : clause->tail_atoms)
            if (tail_exclusions.count(tail) && !tail_exclusions.at(tail).empty())
                result[tail] = tail_exclusions.at(tail);
    return result;
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

std::vector<std::vector<int>> CNF::get_cert_snapshot() const
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

void validate_degree(int positive, int negative, LitType type)
{
    if (positive < 1 || negative < 1 || positive > MAX_MASK_BITS ||
        negative > MAX_MASK_BITS - positive)
        throw invalid_argument("degrees must be positive and total at most 30");
    if (type == SINGLETON && negative != 1)
        throw invalid_argument("SINGLETON requires negative degree 1");
}

static void validate_mask_input(const CNF &cnf, const vector<int> &ids)
{
    if (cnf.clauses.size() > MAX_MASK_BITS || ids.size() > MAX_MASK_BITS)
        throw invalid_argument("branch masks support at most 30 clauses and 30 variables");
    set<int> unique_ids(ids.begin(), ids.end());
    if (unique_ids.size() != ids.size() ||
        any_of(ids.begin(), ids.end(), [](int id) { return id < 2; }))
        throw invalid_argument("branch variables must be distinct ordinary IDs");
}

void calculate_variants(CNF &cnf, vector<int> &ids, vector<int> &clauses_mask,
                        vector<int> &reduced_clauses,
                        vector<int> &no_clauses_mask)
{
    validate_mask_input(cnf, ids);
    int k = ids.size();
    size_t count = size_t(1) << k;
    if (clauses_mask.size() != count || reduced_clauses.size() != count ||
        no_clauses_mask.size() != count)
        throw invalid_argument("incorrect assignment mask buffer size");

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

// Compare scores at the SAME valuation of every unassigned literal/tail.
// Unchanged clauses cancel. A clause gained from a guaranteed-false clause
// pays for one possibly lost satisfied clause. This subsumes both satisfied-
// set inclusion and the old whole-formula min(other) >= max(row) test.
static vector<int> undominated_assignments(const vector<int> &satisfied,
                                           const vector<int> &falsified,
                                           map<int, int> &subsumptions)
{
    vector<int> yes(satisfied.size()), no(falsified.size()), retained;
    for (int row = 0; row < (int)satisfied.size(); ++row)
    {
        yes[row] = count_set_bits(satisfied[row]);
        no[row] = count_set_bits(falsified[row]);
    }
    for (int row = 0; row < (int)satisfied.size(); ++row)
    {
        bool dominated = false;
        for (int other = 0; other < (int)satisfied.size(); ++other)
        {
            // A successful comparison cannot lower (yes, -no): the
            // unassigned remainder of each clause is fixed across rows.
            // Equal ranks imply reciprocal dominance; retain the smaller
            // row. Every witness then strictly raises this total order,
            // so chains always terminate at a retained assignment.
            if (yes[other] < yes[row] ||
                (yes[other] == yes[row] && no[other] > no[row]) ||
                (yes[other] == yes[row] && no[other] == no[row] && other >= row))
                continue;
            int gains = satisfied[other] & falsified[row];
            int losses = satisfied[row] & ~satisfied[other];
            if (count_set_bits(gains) >= count_set_bits(losses))
            {
                subsumptions[row] = other;
                dominated = true;
                break;
            }
        }
        if (!dominated) retained.push_back(row);
    }
    return retained;
}

ProofNode CNF::branch(vector<int> ids)
{
    validate_mask_input(*this, ids);
    int k = ids.size();

    vector<int> branch;

    vector<int> clauses_mask(1 << k);
    vector<int> reduced_clauses(1 << k);
    vector<int> no_clauses_mask(1 << k);

    calculate_variants(*this, ids, clauses_mask, reduced_clauses,
                       no_clauses_mask);

    std::map<int, int> current_subsumptions;
    vector<int> valid_masks = undominated_assignments(
        clauses_mask, no_clauses_mask, current_subsumptions);
    for (int mask : valid_masks) branch.push_back(reduced_clauses[mask]);

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

// Legacy partition fixture retained only for the groups3 validity test.
vector<string> valid_3_partitions;

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
    try { validate_mask_input(cnf, ids); }
    catch (const invalid_argument &error) { result.error = error.what(); return result; }
    int k = (int)ids.size();
    int group_size = (int)group_masks.size();

    if (group_size == 0 || (group_size & (group_size - 1)) != 0)
    {
        result.error = "group size is not a positive power of two";
        return result;
    }
    if (group_size > MAX_MASK_BITS)
    {
        result.error = "group residual currently requires masks narrower than 31 bits";
        return result;
    }

    set<int> unique_masks(group_masks.begin(), group_masks.end());
    if (any_of(group_masks.begin(), group_masks.end(),
               [k](int mask) { return mask < 0 || mask >= (1 << k); }))
    {
        result.error = "group assignment mask out of range";
        return result;
    }
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
    if (k < 0 || k > MAX_MASK_BITS || group_masks.size() > MAX_MASK_BITS)
    {
        diag = "group masks support at most 30 bits";
        return false;
    }
    if (set<int>(group_masks.begin(), group_masks.end()).size() != group_masks.size() ||
        any_of(group_masks.begin(), group_masks.end(),
               [k](int mask) { return mask < 0 || mask >= (1 << k); }))
    {
        diag = "duplicate or out-of-range assignment mask";
        return false;
    }
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

ProofNode CNF::branch_group(vector<int> ids, int max_groups,
                            bool construct_proof, double q)
{
    validate_mask_input(*this, ids);
    if (max_groups < -1) throw invalid_argument("invalid group-count limit");
    int k = ids.size();
    vector<int> clauses_mask(1 << k), reduced_clauses(1 << k), no_clauses_mask(1 << k);
    calculate_variants(*this, ids, clauses_mask, reduced_clauses, no_clauses_mask);
    std::map<int, int> current_subsumptions;
    vector<int> masks = undominated_assignments(
        clauses_mask, no_clauses_mask, current_subsumptions);

    struct Candidate {
        vector<int> rows;
        vector<int> vec;
        GroupWitness witness;
    };
    vector<Candidate> candidates;
    vector<WeightedGroup> weighted;
    vector<int> retained_index(1 << k, -1);
    for (int i = 0; i < (int)masks.size(); ++i) retained_index[masks[i]] = i;

    // Enumerate images over ALL assignments. A useful group may also contain
    // dominated rows; only its intersection with retained rows needs covering.
    enumerate_substitution_groups(k, [&](const vector<int> &group_subst_masks) {
        vector<int> coverage;
        for (int row : group_subst_masks)
            if (retained_index[row] >= 0) coverage.push_back(retained_index[row]);
        if (coverage.empty()) return;
        GroupResidual group_residual =
            materialize_group_residual(*this, ids, group_subst_masks);
        if (!group_residual.valid)
        {
            if (group_residual.cnf) destroy_cnf(group_residual.cnf);
            return;
        }
        unique_ptr<CNF, void (*)(CNF *)> residual_guard(group_residual.cnf, destroy_cnf);
        vector<pair<vector<int>, GroupWitness>> extra_choices;

        if (group_subst_masks.size() >= 2 && MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)
        {
            for (const DirectLemmaResult &lemma :
                 find_direct_lemma23_candidates(*group_residual.cnf))
            {
                GroupWitness witness;
                witness.rule = lemma.rule;
                witness.lemma_var_id = lemma.pivot_id;
                witness.second_lemma_var_id = lemma.second_pivot_id;
                witness.lemma_local_D = lemma.local_D;
                witness.lemma_pos_count = lemma.pos_count;
                witness.lemma_neg_count = lemma.neg_count;
                witness.claimed_vector = lemma.vec;
                extra_choices.push_back({lemma.vec, witness});
            }
            // Statistics count clauses after representative substitutions,
            // including deduplication of merged literals.
            for (const auto &[id, stats] : analyze_formula(*group_residual.cnf))
            {
                int pos = stats.pos_count, neg = stats.neg_count;
                if (pos < 2 || neg < 2) continue;
                // Lemma 4: i >= j >= 2 and at least j-1 unit clauses
                // on the i-occurrence side give the vector (i, 2j+1).
                for (int direction = 0; direction < 2; ++direction)
                {
                    int j = direction == 0 ? neg : pos;
                    int i = direction == 0 ? pos : neg;
                    int units = direction == 0 ? stats.pos_unit_count : stats.neg_unit_count;
                    if (i < j || units < j - 1) continue;
                    GroupWitness witness;
                    witness.rule = "lemma4";
                    witness.lemma_var_id = id;
                    witness.lemma_local_D = j;
                    witness.lemma_pos_count = pos;
                    witness.lemma_neg_count = neg;
                    witness.claimed_vector = {i, 2 * j + 1};
                    extra_choices.push_back({witness.claimed_vector, witness});
                }
            }
        }

        // Each group is analyzed once. Shared residual formulas still go through
        // the formula cache, independent of their assignment images.
        auto residual_proof = make_shared<ProofNode>(
            analyze_residual(*group_residual.cnf, 1, q));
        GroupWitness search_witness;
        search_witness.rule = "residual_search";
        search_witness.claimed_vector = residual_proof->vec;
        search_witness.residual_proof = move(residual_proof);
        extra_choices.push_back({search_witness.claimed_vector, move(search_witness)});

        int base = group_residual.base_decrease;
        vector<int> best_vec;
        GroupWitness best_witness;
        long double best_weight = numeric_limits<long double>::infinity();
        auto consider = [&](vector<int> vec, GroupWitness witness) {
            for (int &value : vec) value += base;
            if (vec.empty() || any_of(vec.begin(),vec.end(),[](int d){return d<0;})) return;
            if (any_of(vec.begin(),vec.end(),[](int d){return d==0;}) &&
                !(witness.rule=="residual_search" && witness.residual_proof &&
                  proof_establishes_progress(*witness.residual_proof))) return;
            long double weight = branching_weight(vec, q);
            if (weight < best_weight)
            {
                best_weight = weight;
                best_vec = move(vec);
                witness.basic_reduce_val = base;
                best_witness = move(witness);
            }
        };
        GroupWitness basic;
        basic.rule = "basic";
        consider({0}, basic);
        for (auto &choice : extra_choices) consider(move(choice.first), move(choice.second));
        if (best_vec.empty()) return;
        candidates.push_back({group_subst_masks, move(best_vec), move(best_witness)});
        weighted.push_back({move(coverage), best_weight});
    });

    GroupCover cover = minimum_group_cover(masks.size(), weighted, max_groups);
    ProofNode direct_child_search = this->xiao_branch(1, "", q);
    if (cover.groups.empty() || branching_weight(direct_child_search.vec, q) < cover.weight)
        return direct_child_search;

    ProofNode node;
    node.type = construct_proof ? "enumeration" : "leaf";
    node.branch_ids = ids;
    node.formula_snapshot = this->get_cert_snapshot();
    node.subsumptions = move(current_subsumptions);
    // `partition` belongs to plain branching. Overlapping groups are recorded
    // explicitly here and in each constructive alternative's represented_masks.
    for (int index : cover.groups)
    {
        const Candidate &candidate = candidates[index];
        node.cover_groups.push_back(candidate.rows);
        node.vec.insert(node.vec.end(), candidate.vec.begin(), candidate.vec.end());
        node.group_witnesses.push_back(candidate.witness);
        if (!construct_proof) continue;
        GroupResidual residual = materialize_group_residual(*this, ids, candidate.rows);
        if (!residual.valid)
        {
            if (residual.cnf) destroy_cnf(residual.cnf);
            throw logic_error("winning cover contains an invalid substitution group");
        }
        unique_ptr<CNF, void (*)(CNF *)> residual_guard(residual.cnf, destroy_cnf);
        const GroupWitness &witness = candidate.witness;
        ProofNode child;
        if (witness.rule == "basic")
        {
            child = ProofNode({0});
            child.formula_snapshot = residual.cnf->get_cert_snapshot();
        }
        else if (witness.rule == "residual_search")
        {
            if (!witness.residual_proof ||
                witness.residual_proof->formula_snapshot != residual.cnf->get_cert_snapshot())
                throw logic_error("residual search proof does not match the winning group");
            child = *witness.residual_proof;
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
        alternative.represented_masks = candidate.rows;
        alternative.proof = make_shared<ProofNode>(move(child));
        node.alternatives.push_back(move(alternative));
    }
    node.tau = branching_factor(node.vec);
    return node;
}

long double branching_weight(const vector<int> &a, double q)
{
    if (!std::isfinite(q) || q <= 1.0)
        throw invalid_argument("branching target must be finite and greater than one");
    if (a.empty()) return std::numeric_limits<long double>::infinity();
    long double total = 0.0L;
    for (int decrease : a)
        total += powl((long double)q, -(long double)decrease);
    return total;
}

bool meets_branching_target(const vector<int> &a, double q, long double weight_target)
{
    if (!std::isfinite(weight_target) || weight_target <= 0)
        throw invalid_argument("weight target must be finite and positive");
    // A call has weight one but does not establish a progressing strategy.
    return !a.empty() && all_of(a.begin(), a.end(), [](int d) { return d > 0; }) &&
           branching_weight(a, q) <= weight_target;
}

bool proof_establishes_progress(const ProofNode &p)
{
    if (p.type=="restart") return MaxSATSettings.ALLOW_POLYNOMIAL_RESTARTS;
    if (p.type=="divide_clause") return !p.children.empty() && all_of(p.children.begin(),p.children.end(),proof_establishes_progress);
    if (p.type=="reduction" && p.children.size()==1)
        return p.formula_snapshot.size()>p.children[0].formula_snapshot.size() || proof_establishes_progress(p.children[0]);
    if (p.type=="enumeration" && !p.alternatives.empty())
        return all_of(p.alternatives.begin(),p.alternatives.end(),[](const auto &a){return a.decrease>0 || (a.proof && proof_establishes_progress(*a.proof));});
    if ((p.type=="branch" || p.type=="xiao_property2_branch" || p.type=="xiao_property1_branch") && p.children.size()==2)
        return (p.reduced_cnt_true>0 || (!p.property2_sides.empty() && p.property2_sides[0]) || proof_establishes_progress(p.children[0])) &&
               (p.reduced_cnt_false>0 || (p.property2_sides.size()>1 && p.property2_sides[1]) || proof_establishes_progress(p.children[1]));
    return !p.vec.empty() && all_of(p.vec.begin(),p.vec.end(),[](int d){return d>0;});
}

bool meets_strategy_target(const ProofNode &p,double q,long double target)
{
    if (!std::isfinite(target) || target<=0) throw invalid_argument("weight target must be finite and positive");
    return !p.vec.empty() && all_of(p.vec.begin(),p.vec.end(),[](int d){return d>=0;}) &&
           branching_weight(p.vec,q)<=target && proof_establishes_progress(p);
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
    for (const auto &[tail, types] : cnf.active_tail_exclusions())
    {
        vector<int> indices;
        for (size_t i = 0; i < cnf.clauses.size(); ++i)
            if (cnf.clauses[i]->tail_atoms.count(tail)) indices.push_back(int(i));
        cout << "Хвост в клозе" << (indices.size() > 1 ? "ах" : "") << " [";
        for (size_t i = 0; i < indices.size(); ++i) cout << (i ? "," : "") << indices[i];
        cout << "]: нет литералов типов ";
        bool first = true;
        for (const auto &d : types) {
            cout << (first ? "" : ", ") << '(' << d[0] << ',' << d[1] << ") "
                 << (d[2] ? "SINGLETON" : "ANY");
            first = false;
        }
        cout << '\n';
    }
}

static unordered_map<string, long long> used_node_storage;
unordered_map<string, long long> *used_nodes = &used_node_storage;
static size_t exposure_child_limit = std::numeric_limits<size_t>::max();
void set_exposure_child_limit(size_t limit) { exposure_child_limit = limit; }

void clear_exposure_deduplication() { used_nodes->clear(); }

void preprocess(int maximum_clause_size)
{
    used_nodes->clear();
    valid_3_partitions.clear();
    ID2VAR[0] = "?";
    VAR2ID["?"] = 0;
    ID2VAR[1] = "?+";
    VAR2ID["?+"] = 1;

    MaxSATSettings.MAXIMUM_CLAUSE_SIZE = maximum_clause_size;
    MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = true;
    MaxSATSettings.ALLOW_LEMMA3_SPLIT = true;
    MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT = false;
    MaxSATSettings.ALLOW_XIAO_PROPERTY2 = false;
    MaxSATSettings.ALLOW_XIAO_PROPERTY1 = false;
    MaxSATSettings.ALLOW_POLYNOMIAL_RESTARTS = false;

    POSSIBLE_LITERALS = {{3, 1, SINGLETON},
                         {2, 2, ANY},       {3, 2, ANY},
                         {2, 3, ANY},
                         {4, 1, SINGLETON}, {2, 1, ANY},
                         {2, 1, SINGLETON}};

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
            for (const auto &[tail, nonempty] : clause->tail_atoms)
                if (cnf->tail_exclusions.count(tail))
                    for (const auto &d : cnf->tail_exclusions.at(tail))
                        lits_str.push_back("exclude:" + to_string(d[0]) + ":" +
                                           to_string(d[1]) + ":" + to_string(d[2]));
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

// A shown literal may not be taken from a tail excluding its type. If ANY
// partially overlaps an excluded singleton type, retain its non-singleton
// subcase by requiring the unique opposite clause to be non-unit.
static bool respects_tail_exclusions(const CNF &parent, CNF &child, int variable,
                                    int positive, int negative)
{
    if (parent.tail_exclusions.empty()) return true;
    for (size_t index = 0; index < parent.clauses.size(); ++index)
        for (bool inv : {false, true})
        {
            if (!child.clauses[index]->lits.count(intern_literal(variable, inv))) continue;
            int p = inv ? negative : positive, n = inv ? positive : negative;
            for (const auto &[tail, flag] : parent.clauses[index]->tail_atoms)
            {
                auto found = parent.tail_exclusions.find(tail);
                if (found == parent.tail_exclusions.end()) continue;
                for (const auto &d : found->second)
                {
                    if (d[0] != p || d[1] != n) continue;
                    if (!d[2]) return false;
                    if (n != 1) continue;
                    for (auto *clause : child.clauses)
                    {
                        if (!clause->lits.count(intern_literal(variable, !inv))) continue;
                        int known = 0;
                        for (auto *lit : clause->lits) known += !is_any_unknown_literal(lit);
                        if (known > 1) continue;
                        if (clause->tail_atoms.empty()) return false;
                        // Structural exposure has a single clause-local tail.
                        if (clause->tail_atoms.size() != 1)
                            throw logic_error("singleton exclusion needs one opposite tail");
                        clause->tail_atoms.begin()->second = true;
                        clause->lits.erase(&UNKNOWN_LITERAL);
                        clause->lits.insert(&UNKNOWN_NOT_EMPTY_LITERAL);
                    }
                }
            }
        }
    return true;
}

vector<CNF *> add_new_var_universal(CNF *cnf, string v_name, int i, int j,
                                    LitType type, int pos,
                                    bool only_pos, bool silent,
                                    vector<long long> &out_children_ids)
{
    validate_degree(i, j, type);
    if (!silent && out.is_open() && !cnf->clauses.empty())
        throw invalid_argument("add declares the root family only; use addpos");
    if (cnf->clauses.size() > MAX_MASK_BITS)
        throw invalid_argument("exposure supports at most 30 parent clauses");
    // a + b = s
    // В 0 <= a <= i клозах литерал встречается с x
    // В 0 <= b <= j клозах он встречается с ~x
    // Остальное в новых клозах

    vector<CNF *> ans;

    Literal named(v_name);
    if (analyze_formula(*cnf).count(named.id))
        throw invalid_argument("exposure variable already occurs in parent");
    Literal *new_lit = intern_literal(named.id, false);
    Literal *new_lit_neg = intern_literal(named.id, true);

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

                    unique_ptr<CNF, decltype(&destroy_cnf)> owner(new CNF(*cnf), destroy_cnf);
                    CNF *now_cnf = owner.get();

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

                    if (!respects_tail_exclusions(*cnf, *now_cnf, named.id, i, j))
                        continue;
                    string now_cnf_str = cnf_to_max_string(now_cnf);

                    if (used_nodes->find(now_cnf_str) == used_nodes->end())
                    {
                        ans.push_back(owner.release());
                        (*used_nodes)[now_cnf_str] = now_cnf->node_id;
                        if (used_nodes->size() > exposure_child_limit) throw ExposureLimitExceeded();
                        out_children_ids.push_back(now_cnf->node_id); // Сохраняем ID нового графа
                    }
                    else
                    {
                        // Граф изоморфен! Линкуем родителя со старым узлом, чтобы не рвать топологию
                        out_children_ids.push_back((*used_nodes)[now_cnf_str]);
                        // owner frees the duplicate and all of its clauses.
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
        global_logger.log_add_variable(cnf->node_id, cnf->get_cert_snapshot(), VAR2ID[v_name], i, j, type, unique_children_ids);
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
                     vector<LiteralDegType> variants, vector<long long> *child_ids)
{
    int pos = need_index_func(cnf);

    // This formula has no wildcard clause satisfying the positional query.
    // Keep it in the frontier unchanged instead of silently exposing the new
    // variable in clause zero (which does not satisfy the query).
    if (pos < 0) {
        if (child_ids) *child_ids={cnf->node_id};
        return {cnf};
    }

    if (pos >= (int)cnf->clauses.size())
        throw invalid_argument("exposure clause out of range");
    Clause *selected = cnf->clauses[pos];
    bool active = any_of(selected->lits.begin(), selected->lits.end(),
                         [](Literal *lit) { return !is_any_unknown_literal(lit); });
    if (!active || selected->tail_atoms.size() != 1 ||
        (!selected->lits.count(&UNKNOWN_LITERAL) &&
         !selected->lits.count(&UNKNOWN_NOT_EMPTY_LITERAL)))
        throw invalid_argument("exposure requires an active literal and one tail");
    if (variants.empty())
        throw invalid_argument("exposure requires a nonempty degree specification");
    for (auto degree : variants) validate_degree(degree.i, degree.j, degree.type);

    vector<CNF *> ans;

    vector<long long> all_children_ids;
    
    for (LiteralDegType l : variants) {
        auto new_vars = add_new_var_universal(cnf, v_name, l.i, l.j, l.type, pos, true, true, all_children_ids);
        ans.insert(ans.end(), new_vars.begin(), new_vars.end());
    }

    if (selected->lits.count(&UNKNOWN_LITERAL))
    {
        CNF *cnf_empty_space = new CNF(*cnf);
        cnf_empty_space->clauses[pos]->lits.erase(&UNKNOWN_LITERAL);
        cnf_empty_space->clauses[pos]->tail_atoms.clear();
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

    if (child_ids) *child_ids=unique_children_ids;
    global_logger.log_addpos(cnf->node_id, cnf->get_cert_snapshot(), VAR2ID[v_name], pos, variants, unique_children_ids, cnf->active_tail_exclusions());

    return ans;
}

vector<CNF *> expose_type_in_place(CNF *cnf, string name,
    const std::function<int(CNF *)> &position, LiteralDegType degree,
    const vector<LiteralDegType> &scope, vector<long long> *child_ids)
{
    validate_degree(degree.i, degree.j, degree.type);
    if (none_of(scope.begin(), scope.end(), [&](const auto &d) {
            return d.i == degree.i && d.j == degree.j && d.type == degree.type;
        })) throw invalid_argument("expose_type: type is not in the current degree family");
    int pos = position(cnf);
    if (pos < 0) {
        if (child_ids) *child_ids = {cnf->node_id};
        return {cnf};
    }
    if (pos >= int(cnf->clauses.size()) || cnf->clauses[pos]->tail_atoms.size() != 1)
        throw invalid_argument("expose_type requires a clause-local single tail");
    if (none_of(cnf->clauses[pos]->lits.begin(), cnf->clauses[pos]->lits.end(),
                [](Literal *lit) { return !is_any_unknown_literal(lit); }))
        throw invalid_argument("expose_type requires an active literal");
    // Structural exposure cannot allocate placements into correlated atoms.
    set<int> seen;
    for (auto *clause : cnf->clauses)
    {
        if (clause->tail_atoms.size() > 1)
            throw invalid_argument("expose_type requires clause-local single tails");
        for (const auto &[tail, flag] : clause->tail_atoms)
            if (!seen.insert(tail).second)
                throw invalid_argument("expose_type requires independent clause-local tails");
    }
    int tail = cnf->clauses[pos]->tail_atoms.begin()->first;
    array<int, 3> requested = {degree.i, degree.j, degree.type == SINGLETON};
    if (cnf->tail_exclusions.count(tail))
        for (const auto &d : cnf->tail_exclusions.at(tail))
            if (d[0] == requested[0] && d[1] == requested[1] && (!d[2] || requested[2])) {
                if (child_ids) *child_ids = {cnf->node_id};
                return {cnf};
            }
    vector<long long> children;
    auto present = add_new_var_universal(cnf, name, degree.i, degree.j,
                                         degree.type, pos, true, true, children);
    CNF *absent = new CNF(*cnf);
    absent->tail_exclusions[tail].insert(requested);
    present.push_back(absent);
    children.push_back(absent->node_id);
    sort(children.begin(), children.end());
    children.erase(unique(children.begin(), children.end()), children.end());
    if (child_ids) *child_ids = children;
    global_logger.log_expose_type(*cnf, VAR2ID.at(name), pos, degree, scope, children);
    return present;
}

// Функция возвращает пару {CNF_с_пустотой, CNF_с_непустотой(?+)}
DivideResult empty_divide(CNF *cnf, double q, int group_limit)
{
    if (group_limit < 0 || group_limit > MAX_MASK_BITS)
        throw invalid_argument("invalid split group-variable limit");
    DivideResult best_split;
    long double min_worst_weight = std::numeric_limits<long double>::infinity();

    vector<int> ids;
    for (auto p : ID2VAR)
    {
        if (p.first != UNKNOWN_LITERAL.id && p.first != UNKNOWN_NOT_EMPTY_LITERAL.id)
        {
            ids.push_back(p.first);
        }
    }

    auto best_weight = [&](CNF *candidate)
    {
        long double result;
        {
            ProofNode node = candidate->xiao_branch(1, "x", q);
            result = branching_weight(node.vec, q);
        }
        if (ids.size() <= static_cast<std::size_t>(group_limit))
        {
            ProofNode node = candidate->branch_group(ids, -1, false, q);
            result = min(result, branching_weight(node.vec, q));
        }
        return result;
    };

    auto best_proof = [&](CNF *candidate)
    {
        long double xiao_weight;
        {
            ProofNode node = candidate->xiao_branch(1, "x", q);
            xiao_weight = branching_weight(node.vec, q);
        }
        if (ids.size() <= static_cast<std::size_t>(group_limit))
        {
            ProofNode group_node = candidate->branch_group(ids, -1, false, q);
            if (branching_weight(group_node.vec, q) <= xiao_weight)
                return candidate->branch_group(ids, -1, true, q);
        }
        return candidate->xiao_branch(1, "x", q);
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
            long double worst_weight = max(best_weight(cnf_empty),
                                           best_weight(cnf_not_empty));

            if (worst_weight < min_worst_weight)
            {
                min_worst_weight = worst_weight;

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
        const ProofNode &worst = branching_weight(best_split.proof_tree.children[0].vec, q) >=
                                branching_weight(best_split.proof_tree.children[1].vec, q)
                                    ? best_split.proof_tree.children[0]
                                    : best_split.proof_tree.children[1];
        best_split.proof_tree.vec = worst.vec;
        best_split.proof_tree.tau = branching_factor(worst.vec);
        remember_lemma_candidate(best_split.cnf_empty->node_id, best_split.proof_tree.children[0]);
        remember_lemma_candidate(best_split.cnf_not_empty->node_id, best_split.proof_tree.children[1]);

        global_logger.log_divide(cnf->node_id, cnf->get_cert_snapshot(),
                                 best_split.proof_tree.target_clause_idx,
                                 best_split.cnf_empty->node_id,
                                 best_split.cnf_not_empty->node_id,
                                 cnf->active_tail_exclusions());
    }

    return best_split;
}
