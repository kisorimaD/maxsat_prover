#include "cnf.h"
#include <algorithm>
#include <map>
#include <vector>
#include <set>

using namespace std;

struct VarStats {
    int pos_count = 0;      // Число вхождений x
    int neg_count = 0;      // Число вхождений ~x
    int pos_unit_count = 0; // Число unit-клоз {x}
    int neg_unit_count = 0; // Число unit-клоз {~x}
    
    // Индексы клоз, где встречается переменная
    vector<int> pos_indices;
    vector<int> neg_indices;
};

// Проверка: C1 \ {l1} == C2 \ {l2}
// Используется для RR4
bool are_clauses_resolvable(Clause* c1, int var_id, bool inv1, Clause* c2, bool inv2) {
    // Собираем литералы первого клоза без var_id
    vector<Literal*> lits1;
    for (auto l : c1->lits) {
        if (l == &UNKNOWN_LITERAL) { return false; } // Мы не можем ничего сказать про равенство, если в одной из клоз есть неизвестный литерал
        if (l->id == var_id && l->inv == inv1) continue;
        lits1.push_back(l);
    }

    // Собираем литералы второго клоза без var_id
    vector<Literal*> lits2;
    for (auto l : c2->lits) {
        if (l == &UNKNOWN_LITERAL) { return false; }
        if (l->id == var_id && l->inv == inv2) continue;
        lits2.push_back(l);
    }

    if (lits1.size() != lits2.size()) return false;

    // Сравнение. Так как lits в Clause хранятся в set (упорядочено по LiteralPtrLess), 
    // но здесь мы извлекли их в vector, порядок мог нарушиться, если мы итерировались не по set.
    // Однако в классе Clause поле lits это set. Итерация по set дает упорядоченную последовательность.
    // Мы просто пропускаем один элемент. Порядок остальных сохраняется.
    
    for (size_t i = 0; i < lits1.size(); ++i) {
        if (lits1[i] == &UNKNOWN_LITERAL && lits2[i] == &UNKNOWN_LITERAL) continue;
        if (lits1[i] == &UNKNOWN_LITERAL || lits2[i] == &UNKNOWN_LITERAL) return false;
        
        if (lits1[i]->id != lits2[i]->id || lits1[i]->inv != lits2[i]->inv) {
            return false;
        }
    }
    return true;
}

// Применение присваивания переменной var_id значения value (true/false)
// Возвращает пару: <количество удовлетворенных (удаленных) клоз, указатель на новый CNF>
pair<int, CNF*> apply_xiao_assignment(CNF* original, int var_id, bool val_to_set) {
    // val_to_set = true -> x=1. Литералы x (inv=false) становятся True (клоза удаляется). 
    // Литералы ~x (inv=true) становятся False (литерал удаляется из клозы).
    
    CNF* new_cnf = new CNF();
    int satisfied_cnt = 0;

    for (Clause* c : original->clauses) {
        bool satisfied = false;
        vector<Literal*> new_lits_vec;

        for (Literal* l : c->lits) {
            if (l == &UNKNOWN_LITERAL) {
                new_lits_vec.push_back(l);
                continue;
            }

            if (l->id == var_id) {
                // Если полярность совпадает с присваиваемым значением (x и x=1, или ~x и x=0)
                // То клоза удовлетворена
                // val_to_set = true (1), l->inv = false (x) -> match
                // val_to_set = false (0), l->inv = true (~x) -> match
                bool is_lit_true = (val_to_set && !l->inv) || (!val_to_set && l->inv);
                
                if (is_lit_true) {
                    satisfied = true;
                    break;
                }
                // Если литерал ложный, мы его просто не добавляем в new_lits_vec
            } else {
                new_lits_vec.push_back(l);
            }
        }

        if (satisfied || new_lits_vec.empty()) { // либо выполнили клозу, либо там нет '?' и все остальные клозы убрали => можем откинуть клозу
            satisfied_cnt++;
        } else {
            // Клоза не удовлетворена, добавляем её (возможно урезанную) в новый CNF
            // Если вектор пуст или содержит только '?', надо проверить

            // Если осталось '?' то просто не будем её дальше рассматривать, но это не засчитывается за удалённую клозу
            if(new_lits_vec.size() == 1 && new_lits_vec[0] == &UNKNOWN_LITERAL)
            {
                continue;
            }

            Clause* new_c = new Clause(new_lits_vec);
            // Если клоза стала пустой (конфликт), в MaxSAT это просто остается клозой, которую нельзя удовлетворить.
            // В рамках бренчинга мы просто считаем reduced clauses.
            new_cnf->clauses.push_back(new_c);
        }
    }
    return {satisfied_cnt, new_cnf};
}


vector<int> CNF::xiao_branch(int depth) {
    // 1. Сбор статистики
    map<int, VarStats> stats; // id переводит в структуру с полной информацией о переменной
    
    // Инициализация ключей мапы, чтобы не пропустить переменные
    for (Clause* c : clauses) {
        for (Literal* l : c->lits) {
            if (l != &UNKNOWN_LITERAL) stats[l->id]; 
        }
    }

    for (int i = 0; i < (int)clauses.size(); ++i) {
        Clause* c = clauses[i];
        bool is_unit = (c->lits.size() == 1 && *c->lits.begin() != &UNKNOWN_LITERAL);
        // Примечание: если в клозе есть '?', она не считается строгой unit-клозой для RR3
        
        for (Literal* l : c->lits) {
            if (l == &UNKNOWN_LITERAL) continue;
            
            VarStats& s = stats[l->id];
            if (l->inv) {
                s.neg_count++;
                s.neg_indices.push_back(i);
                if (is_unit) s.neg_unit_count++;
            } else {
                s.pos_count++;
                s.pos_indices.push_back(i);
                if (is_unit) s.pos_unit_count++;
            }
        }
    }

    // --- Reduction Rules ---

    // RR 3: Если (i, j)-литерал x, и >= j unit-клоз {x}, то x=1.
    // Редукция: удаляем i клоз (где x=1). 
    for (auto const& [id, s] : stats) {
        // Проверка для положительного литерала x
        if (s.pos_count > 0 && s.pos_unit_count >= s.neg_count) {
            return { s.pos_count };
        }
        // Проверка для отрицательного литерала ~x (симметрично)
        if (s.neg_count > 0 && s.neg_unit_count >= s.pos_count) {
            return { s.neg_count };
        }
    }

    // RR 4: (F' ^ xC ^ ~xC) -> (F' ^ C). Редукция на 1 клозу.
    for (auto const& [id, s] : stats) {
        if (s.pos_count > 0 && s.neg_count > 0) {
            // Перебор пар клоз
            for (int idx_pos : s.pos_indices) {
                for (int idx_neg : s.neg_indices) {
                    Clause* c_pos = clauses[idx_pos];
                    Clause* c_neg = clauses[idx_neg];
                    
                    // Проверяем, равны ли клозы за вычетом x и ~x
                    if (are_clauses_resolvable(c_pos, id, false, c_neg, true)) {
                        return { 1 };
                    }
                }
            }
        }
    }

    // RR 6: Если есть (i, 1)-литерал x, и клоза с ~x содержит (j, 1)-литерал y
    // Формула: ... ^ xC... ^ ~xyD -> ... ^ yCD
    // Редукция на 1 клозу (было i+1, стало i клоз yCD).
    for (auto const& [id, s] : stats) {
        // Случай A: x имеет распределение (i, 1) -> ~x встречается 1 раз
        if (s.neg_count == 1) {
            int c_idx = s.neg_indices[0];
            Clause* c = clauses[c_idx]; // Клоза, содержащая ~x
            
            // Ищем y в этой клозе
            for (Literal* l_y : c->lits) {
                if (l_y == &UNKNOWN_LITERAL) continue;
                if (l_y->id == id) continue; // Это сам ~x
                
                // Проверяем, является ли y (j, 1)-литералом.
                
                VarStats& sy = stats[l_y->id];
                bool condition_met = false;
                
                if (l_y->inv) { // y негативный в C
                     if (sy.pos_count == 1) condition_met = true;
                } else { // y позитивный в C
                     if (sy.neg_count == 1) condition_met = true;
                }
                
                if (condition_met) {
                    return { 1 };
                }
            }
        }
        
        // Случай B: x имеет распределение (1, i) -> x встречается 1 раз (симметрично)
        if (s.pos_count == 1) {
            int c_idx = s.pos_indices[0];
            Clause* c = clauses[c_idx]; // Клоза, содержащая x
            
            for (Literal* l_y : c->lits) {
                if (l_y == &UNKNOWN_LITERAL) continue;
                if (l_y->id == id) continue; 
                
                VarStats& sy = stats[l_y->id];
                bool condition_met = false;
                
                if (l_y->inv) { 
                     if (sy.pos_count == 1) condition_met = true;
                } else { 
                     if (sy.neg_count == 1) condition_met = true;
                }
                
                if (condition_met) {
                    return { 1 };
                }
            }
        }
    }

    // Если правила не сработали и глубина 0
    if (depth == 0) {
        return { 0 };
    }

    // --- Branching (если depth > 0 и RR не сработали) ---
    
    vector<int> best_branching;
    double min_tau = 1e18; // Инициализируем большим числом (худшая оценка)
    bool any_var_processed = false;
    int best_branch_var_id = -1;

    // Перебираем каждую переменную как кандидата на ветвление
    for (auto const& [var_id, s] : stats) {
        vector<int> current_branching;

        // Ветвь 1: x = 1 (True)
        {
            // Применяем присваивание: получаем (кол-во удаленных клоз, новый CNF)
            auto [reduced_cnt, new_cnf] = apply_xiao_assignment(this, var_id, true);
            
            // Рекурсивный вызов
            vector<int> child_res = new_cnf->xiao_branch(depth - 1);
            
            // Объединяем результат: к каждому варианту из поддерева добавляем текущее сокращение
            for (int val : child_res) {
                current_branching.push_back(reduced_cnt + val);
            }

            // Очистка памяти
            for(auto c : new_cnf->clauses) delete c;
            delete new_cnf;
        }

        // Ветвь 2: x = 0 (False)
        {
            auto [reduced_cnt, new_cnf] = apply_xiao_assignment(this, var_id, false);
            
            vector<int> child_res = new_cnf->xiao_branch(depth - 1);
            
            for (int val : child_res) {
                current_branching.push_back(reduced_cnt + val);
            }

            for(auto c : new_cnf->clauses) delete c;
            delete new_cnf;
        }

        // Вычисляем branching factor для текущего вектора
        double current_tau = branching_factor(current_branching);

        // Ищем минимум (лучшую оценку сложности)
        if (!any_var_processed || current_tau < min_tau) {
            min_tau = current_tau;
            best_branching = current_branching;
            any_var_processed = true;
            best_branch_var_id = var_id;
        }
    }

    if (!any_var_processed) {
        // Если переменных нет (пустая формула или только '?'), считаем, что редукции нет
        return { 0 };
    }
    
    // Сортируем вектор для детерминированности вывода (по убыванию)
    std::sort(best_branching.begin(), best_branching.end(), std::greater<int>());

    return best_branching;
}