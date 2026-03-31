#include "cnf.h"
#include <algorithm>
#include <map>
#include <vector>
#include <set>

using namespace std;

struct VarStats
{
    int pos_count = 0;      // Число вхождений x
    int neg_count = 0;      // Число вхождений ~x
    int pos_unit_count = 0; // Число unit-клоз {x}
    int neg_unit_count = 0; // Число unit-клоз {~x}

    // Индексы клоз, где встречается переменная
    vector<int> pos_indices;
    vector<int> neg_indices;
};

bool is_any_unknown_literal(Literal *l)
{
    return (l == &UNKNOWN_LITERAL || l == &UNKNOWN_NOT_EMPTY_LITERAL);
}

bool are_clauses_resolvable(Clause *c1, int var_id, bool inv1, Clause *c2, bool inv2)
{
    vector<Literal *> lits1;
    for (auto l : c1->lits)
    {
        if (is_any_unknown_literal(l))
        {
            return false;
        }
        if (l->id == var_id && l->inv == inv1)
            continue;
        lits1.push_back(l);
    }

    vector<Literal *> lits2;
    for (auto l : c2->lits)
    {
        if (is_any_unknown_literal(l))
        {
            return false;
        }
        if (l->id == var_id && l->inv == inv2)
            continue;
        lits2.push_back(l);
    }

    if (lits1.size() != lits2.size())
        return false;

    for (size_t i = 0; i < lits1.size(); ++i)
    {
        if (is_any_unknown_literal(lits1[i]) && is_any_unknown_literal(lits2[i]))
            continue;
        if (is_any_unknown_literal(lits1[i]) || is_any_unknown_literal(lits2[i]))
            return false;

        if (lits1[i]->id != lits2[i]->id || lits1[i]->inv != lits2[i]->inv)
        {
            return false;
        }
    }
    return true;
}

pair<int, CNF *> apply_xiao_assignment(CNF *original, int var_id, bool val_to_set)
{
    CNF *new_cnf = new CNF();
    int satisfied_cnt = 0;

    for (Clause *c : original->clauses)
    {
        bool satisfied = false;
        vector<Literal *> new_lits_vec;

        for (Literal *l : c->lits)
        {
            if (l == &UNKNOWN_LITERAL)
            {
                new_lits_vec.push_back(l);
                continue;
            }

            if (l->id == var_id)
            {
                bool is_lit_true = (val_to_set && !l->inv) || (!val_to_set && l->inv);
                if (is_lit_true)
                {
                    satisfied = true;
                    break;
                }
            }
            else
            {
                new_lits_vec.push_back(l);
            }
        }

        if (satisfied || new_lits_vec.empty())
        {
            satisfied_cnt++;
        }
        else
        {
            if (new_lits_vec.size() == 1 && is_any_unknown_literal(new_lits_vec[0]))
                continue;

            Clause *new_c = new Clause(new_lits_vec);
            new_cnf->clauses.push_back(new_c);
        }
    }
    return {satisfied_cnt, new_cnf};
}

// Новая функция для проверки: является ли переменная (3,2) хорошей (good)
bool is_good_variable(CNF *cnf, int var_id, const VarStats &s)
{
    // Убедимся, что это (3,2)-литерал или (2,3)-литерал
    if (!((s.pos_count == 3 && s.neg_count == 2) || (s.pos_count == 2 && s.neg_count == 3)))
    {
        return false;
    }

    // Выбираем значение, которое удалит именно 3 клозы
    bool val_to_set = (s.pos_count == 3) ? true : false;

    // Удаляем 3 клозы и модифицируем оставшиеся (как при подстановке)
    auto [reduced_cnt, new_cnf] = apply_xiao_assignment(cnf, var_id, val_to_set);

    // Собираем статистику для оставшейся формулы
    map<int, VarStats> temp_stats;
    for (Clause *c : new_cnf->clauses)
    {
        bool is_unit = (c->lits.size() == 1 && is_any_unknown_literal(*c->lits.begin()));
        for (Literal *l : c->lits)
        {
            if (is_any_unknown_literal(l))
                continue;
            VarStats &ts = temp_stats[l->id];
            if (l->inv)
            {
                ts.neg_count++;
                if (is_unit)
                    ts.neg_unit_count++;
            }
            else
            {
                ts.pos_count++;
                if (is_unit)
                    ts.pos_unit_count++;
            }
        }
    }

    bool is_good = false;
    for (auto const &[y_id, y_s] : temp_stats)
    {
        int degree = y_s.pos_count + y_s.neg_count;
        if (degree == 0)
            continue;

        // Условие 1: Степень <= 3
        if (degree <= 3)
        {
            is_good = true;
            break;
        }

        // Условие 2: (i, 1)-not singleton
        // Входит 1 раз позитивно и эта клоза не единичная
        if (y_s.pos_count == 1 && y_s.pos_unit_count == 0)
        {
            is_good = true;
            break;
        }
        // Или входит 1 раз негативно и эта клоза не единичная
        if (y_s.neg_count == 1 && y_s.neg_unit_count == 0)
        {
            is_good = true;
            break;
        }
    }

    // Очистка памяти
    for (auto c : new_cnf->clauses)
        delete c;
    delete new_cnf;

    return is_good;
}

vector<int> CNF::xiao_branch(int depth, std::string first_var)
{
    double granted = 100;
    vector<int> granted_branch = {0};

    map<int, VarStats> stats;

    for (Clause *c : clauses)
    {
        for (Literal *l : c->lits)
        {
            if (!is_any_unknown_literal(l))
                stats[l->id];
        }
    }

    for (int i = 0; i < (int)clauses.size(); ++i)
    {
        Clause *c = clauses[i];
        bool is_unit = (c->lits.size() == 1 && is_any_unknown_literal(*c->lits.begin()));

        for (Literal *l : c->lits)
        {
            if (is_any_unknown_literal(l))
                continue;

            VarStats &s = stats[l->id];
            if (l->inv)
            {
                s.neg_count++;
                s.neg_indices.push_back(i);
                if (is_unit)
                    s.neg_unit_count++;
            }
            else
            {
                s.pos_count++;
                s.pos_indices.push_back(i);
                if (is_unit)
                    s.pos_unit_count++;
            }
        }
    }

    // --- Reduction Rules ---
    // RR 3
    for (auto const &[id, s] : stats)
    {
        if (s.pos_count > 0 && s.pos_unit_count >= s.neg_count)
            return {s.pos_count};
        if (s.neg_count > 0 && s.neg_unit_count >= s.pos_count)
            return {s.neg_count};
    }

    // RR 2
    for (auto const &[id, s] : stats)
    {
        if (s.pos_count == 1 && s.neg_count == 1)
            return {1};
    }

    // RR 4
    for (auto const &[id, s] : stats)
    {
        if (s.pos_count > 0 && s.neg_count > 0)
        {
            for (int idx_pos : s.pos_indices)
            {
                for (int idx_neg : s.neg_indices)
                {
                    if (are_clauses_resolvable(clauses[idx_pos], id, false, clauses[idx_neg], true))
                    {
                        return {1};
                    }
                }
            }
        }
    }

    // RR 6
    for (auto const &[id, s] : stats)
    {
        if (s.neg_count == 1)
        {
            Clause *c = clauses[s.neg_indices[0]];
            for (Literal *l_y : c->lits)
            {
                if (is_any_unknown_literal(l_y) || l_y->id == id)
                    continue;
                VarStats &sy = stats[l_y->id];
                bool condition_met = l_y->inv ? (sy.pos_count == 1) : (sy.neg_count == 1);
                if (condition_met)
                    return {1};
            }
        }
        if (s.pos_count == 1)
        {
            Clause *c = clauses[s.pos_indices[0]];
            for (Literal *l_y : c->lits)
            {
                if (is_any_unknown_literal(l_y) || l_y->id == id)
                    continue;
                VarStats &sy = stats[l_y->id];
                bool condition_met = l_y->inv ? (sy.pos_count == 1) : (sy.neg_count == 1);
                if (condition_met)
                    return {1};
            }
        }
    }

    // Step 4
    for (auto const &[id, s] : stats)
    {
        if (s.neg_count == 2 && s.pos_count == 2)
        {
            if (s.neg_unit_count >= 1 || s.pos_unit_count >= 1)
            {
                vector<int> step4_branch = {3, 3};
                if (branching_factor(step4_branch) < granted)
                {
                    granted = branching_factor(step4_branch);
                    granted_branch = step4_branch;
                }
            }
        }
        else if (s.pos_count == 3 && s.neg_count == 2 && s.neg_unit_count >= 1)
        {
            vector<int> step4_branch = {5, 2};
            if (branching_factor(step4_branch) < granted)
            {
                granted = branching_factor(step4_branch);
                granted_branch = step4_branch;
            }
        }
        else if (s.neg_count == 3 && s.pos_count == 2 && s.pos_unit_count >= 1)
        {
            vector<int> step4_branch = {5, 2};

            if (branching_factor(step4_branch) < granted)
            {
                granted = branching_factor(step4_branch);
                granted_branch = step4_branch;
            }
        }
    }

    if (depth == 0)
        return granted_branch;

    // --- Анализ Good Variables перед бренчингом ---
    map<int, bool> is_good_var;
    bool any_good_exists = false;

    // Проверяем все переменные, чтобы узнать, есть ли хотя бы одна good
    for (auto const &[var_id, s] : stats)
    {
        is_good_var[var_id] = false;
        if ((s.pos_count == 3 && s.neg_count == 2) || (s.pos_count == 2 && s.neg_count == 3))
        {
            bool good = is_good_variable(this, var_id, s);
            is_good_var[var_id] = good;
            if (good)
                any_good_exists = true;
        }
    }

    // --- Branching ---

    vector<int> best_branching;
    double min_tau = 1e18;
    bool any_var_processed = false;
    int best_branch_var_id = -1;

    for (auto const &[var_id, s] : stats)
    {
        vector<int> current_branching;

        // Является ли текущая переменная целевой переменной x (first_var)?
        bool is_target_var = false;
        auto it = ID2VAR.find(var_id);
        if (it != ID2VAR.end() && it->second == first_var)
        {
            is_target_var = true;
        }

        // Проверяем, должны ли мы применять бесплатное ветвление (3,3) для целевой переменной
        bool is_3_2_var = ((s.pos_count == 3 && s.neg_count == 2) || (s.pos_count == 2 && s.neg_count == 3));
        bool apply_heuristic = is_target_var && is_3_2_var && !is_good_var[var_id] && any_good_exists;

        // Ветвь 1: x = 1 (True)

        auto [reduced_cnt1, new_cnf1] = apply_xiao_assignment(this, var_id, true);
        // Передаем пустую строку, чтобы предотвратить применение этого трюка на нижних уровнях
        vector<int> child1_res = new_cnf1->xiao_branch(depth - 1, "");

        vector<int> stop1_res = (depth != 1) ? new_cnf1->xiao_branch(0, "") : child1_res;

        // Если x=1 — это та самая ветка, где удаляются 3 клозы
        if (apply_heuristic && s.pos_count == 3)
        {
            double tau_child = branching_factor(child1_res);
            double tau_33 = branching_factor({3, 3});
            if (tau_33 < tau_child)
            {
                child1_res = {3, 3}; // Подмена рекурсивного ответа на бесплатное ветвление (3,3)
            }
        }

        // for (int val : child_res)
        // {
        //     current_branching.push_back(reduced_cnt + val);
        // }
        // for (auto c : new_cnf->clauses)
        //     delete c;
        // delete new_cnf;

        // Ветвь 2: x = 0 (False)

        auto [reduced_cnt0, new_cnf0] = apply_xiao_assignment(this, var_id, false);
        // Передаем пустую строку для дочерних узлов
        vector<int> child0_res = new_cnf0->xiao_branch(depth - 1, "");
        vector<int> stop0_res = (depth != 1) ? new_cnf0->xiao_branch(0, "") : child0_res;

        // Если x=0 — это та самая ветка, где удаляются 3 клозы
        if (apply_heuristic && s.neg_count == 3)
        {
            double tau_child = branching_factor(child0_res);
            double tau_33 = branching_factor({3, 3});
            if (tau_33 < tau_child)
            {
                child0_res = {3, 3}; // Подмена на бесплатное ветвление (3,3)
            }
        }

        // for (int val : child_res)
        // {
        //     current_branching.push_back(reduced_cnt + val);
        // }
        // for (auto c : new_cnf->clauses)
        //     delete c;
        // delete new_cnf;

        double current_tau = 100;

        for (vector<int> f : {child1_res, stop1_res})
        {
            for (vector<int> s : {child0_res, stop0_res})
            {
                current_branching.clear();
                for (int el : f)
                    current_branching.push_back(reduced_cnt1 + el);
                for (int el : s)
                    current_branching.push_back(reduced_cnt0 + el);

                current_tau = branching_factor(current_branching);

                if (!any_var_processed || current_tau < min_tau)
                {
                    min_tau = current_tau;
                    best_branching = current_branching;
                    any_var_processed = true;
                    best_branch_var_id = var_id;
                }
            }
        }
    }

    if (!any_var_processed)
        return {0};

    std::sort(best_branching.begin(), best_branching.end(), std::greater<int>());

    if (branching_factor(best_branching) > granted)
        return granted_branch;

    return best_branching;
}