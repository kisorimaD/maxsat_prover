#include "cli.h"
#include "cnf.h"
#include "cert_logger.h"

#include <algorithm>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace {
void pretty_branch_print(vector<string> &vars, CNF *cnf)
{
    int k = vars.size();

    map<int, int> id2ind;

    for (int i = 0; i < k; ++i)
    {
        id2ind[VAR2ID[vars[i]]] = i;
    }

    print_cnf(*cnf);

    for (int i = 0; i < k; ++i)
    {
        cout << vars[i] << '\t';
    }

    for (int i = 0; i < (int)cnf->clauses.size(); ++i)
    {
        cout << i + 1;
        cout << '\t';
    }

    cout << endl;

    for (int mask = 0; mask < (1 << k); ++mask)
    {
        for (int i = 0; i < k; ++i)
        {
            cout << ((mask >> i) & 1) << '\t';
        }

        for (int i = 0; i < (int)cnf->clauses.size(); ++i)
        {
            bool find_another_literal = false;
            bool find_true = false;

            for (Literal *l : cnf->clauses[i]->lits)
            {
                if (id2ind.count(l->id) != 0)
                {
                    if (((mask >> id2ind[l->id]) & 1) ^ l->inv)
                    {
                        find_true = true;
                    }
                }
                else
                {
                    find_another_literal = true;
                }
            }

            string res = "?";
            if (find_true)
            {
                res = "YES";
            }
            else if (!find_another_literal)
            {
                res = "NO";
            }
            cout << res << '\t';
        }

        cout << endl;
    }
}

function<int(CNF *)> create_pos_func(set<Literal *, LiteralPtrLess> need_lits, set<Literal *, LiteralPtrLess> no_lits)
{
    return [need_lits, no_lits](CNF *cnf)
    {
        for (int i = 0; i < cnf->clauses.size(); ++i)
        {
            Clause *now_clause = cnf->clauses[i];

            if (!now_clause->lits.count(&UNKNOWN_LITERAL) &&
                !now_clause->lits.count(&UNKNOWN_NOT_EMPTY_LITERAL))
            {
                continue;
            }

            bool flag = false;

            // print_clause(*now_clause);

            for (Literal *l : now_clause->lits)
            {

                // cout << "compare(" << (*need_lits.begin())->id << "," << l->id << ") = "
                //      << LiteralPtrLess{}((*need_lits.begin()), l) << " / "
                //      << LiteralPtrLess{}(l, (*need_lits.begin())) << endl;

                if (no_lits.find(l) != no_lits.end())
                {
                    // cout << "break!" << endl;
                    flag = true;
                    break;
                }
            }
            // cout << endl;

            for (Literal *l : need_lits)
            {
                if (now_clause->lits.find(l) == now_clause->lits.end())
                {
                    flag = true;
                    break;
                }
            }

            if (!flag)
                return i;
        }

        return -1;
    };
}

void print_progress(double percentage)
{
    int pb_length = 60;
    int val = static_cast<int>(percentage * 100);
    int lpad = static_cast<int>(percentage * pb_length);
    int rpad = pb_length - lpad;
    std::cout << "\r" << val << "% [" << std::string(lpad, '#') << std::string(rpad, '-') << "]" << std::flush;
}

void branch_epoch_universal(vector<CNF *> &variants, vector<int> &ids, double C, bool is_group_branch)
{
    cout << "Начинается примитивная фильтрация\n";
    vector<CNF *> filtered_variants;

    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        ProofNode naive_node = cnf->branch(ids); // Используем ProofNode

        if (!meets_branching_target(naive_node.vec, C))
        {  
            filtered_variants.push_back(cnf);
        }
        else
        {
            global_logger.log_proof_tree(cnf->node_id, naive_node);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    if (!is_group_branch)
    {
        swap(filtered_variants, variants);
        return;
    }

    cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с группировкой\n";

    bool need_pb = false;
    if (!filtered_variants.empty() &&
        (ids.size() >= 5 || filtered_variants.size() > (1000u >> (2 * ids.size()))))
    {
        need_pb = true;
        cout << "\nWARNING! Слишком большой размер оставшегося массива, бренчинг с группировкой может работать очень медленно.\n\n";
    }

    swap(variants, filtered_variants);
    filtered_variants.clear();

    int vsize = variants.size();


    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        // Analyze the groups once and solve one unrestricted weighted cover.
        // Constructive residual proofs are already retained by group analysis.
        ProofNode group_node = cnf->branch_group(ids, -1, true, C);
        if (!meets_branching_target(group_node.vec, C))
            filtered_variants.push_back(cnf);
        else
            global_logger.log_proof_tree(cnf->node_id, group_node);

        if (need_pb && (i + 1) % 5 == 0)
        {
            print_progress((double)(i + 1) / vsize);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    cout << "Осталось [" << filtered_variants.size() << "]\n\n";

    swap(variants, filtered_variants);

    return;
}

void print_help_universal()
{
    cout << "Список команд:\n";
    cout << "   add [var_name] [i] [j] [SINGLETON | ANY]\t\tЗадать корневое семейство один раз; SINGLETON требует j = 1\n";
    cout << "   addlit [i] [j] [SINGLETON | ANY]       \t\tДобавить тип в список возможных литералов на время запуска\n";
    cout << "   addpos [var_name] [need_names] [no_names]\t\tДобавить новую переменную в первую клозу, в которой есть все\n\t\t\t\t\t\t\tпеременные из need_names и нет ни одной из no_names. Ввод разделяется строчками\n";
    cout << "   sv [mask]                               \t\tУстановить возможные типы литералов по показанной битовой маске\n";
    cout << "   set [branching factor]                  \t\tУстановить порог C (по умолчанию 1.2873)\n";
    cout << "   assumptions [on | off]                 \t\tРазрешить/запретить все named-assumption leaves\n";
    cout << "   branch                                  \t\tОбычное отсеивание + с группировкой бренчингом всех вариантов ниже С\n";
    cout << "   simple_branch                           \t\tОбычное отсеивание без группировки бренчингом всех вариантов ниже С\n";
    cout << "   target [i]                              \t\tОставить в рассмотрении только [i] вариант\n";
    cout << "   head [n]                                \t\tВывести [n] первых вариантов сейчас\n";
    cout << "   print [i]                               \t\tВывести [i] вариант и разобрать по переменным\n";
    cout << "   stats                                   \t\tВывести минимум и максимум branching factor среди оставшихся вариантов\n";
    cout << "   factor [vector]                         \t\tВывести branching factor для заданного вектора\n";
    cout << "   setposfunc [need_names] [no_names]      \t\tЗафиксировать позиционную функцию, которая будет выводиться в print\n";
    cout << "   empty_divide [i]                        \t\tПрименить empty_divide к [i] формуле (или ко всем, если i = -1)\n";
    cout << "   help                                    \t\tВывести список команд (этот)\n";
    cout << "   exit                                    \t\tВыйти из тестирования\n\n";
}

template<class... Values>
void read_arguments(Values&... values)
{
    if (!(cin >> ... >> values))
        throw runtime_error("Incomplete or invalid command arguments");
}

void read_command_line(string &line)
{
    if (!getline(cin, line))
        throw runtime_error("Incomplete multiline command");
}

// Frontiers borrow pointers; this owner releases formulas once they leave cur.
class FrontierOwner {
    using Owner = unique_ptr<CNF, decltype(&destroy_cnf)>;
    map<CNF*, Owner> owned;
public:
    void adopt(const vector<CNF*> &formulas) {
        for (CNF *formula : formulas)
            if (!owned.count(formula))
                owned.emplace(formula, Owner(formula, destroy_cnf));
    }
    void retain(const vector<CNF*> &formulas) {
        adopt(formulas);
        set<CNF*> live(formulas.begin(), formulas.end());
        for (auto it = owned.begin(); it != owned.end(); )
            if (!live.count(it->first)) it = owned.erase(it);
            else ++it;
    }
};
} // namespace

void run_interactive()
{
    auto posfunc = create_pos_func(set<Literal *, LiteralPtrLess>(), set<Literal *, LiteralPtrLess>());

    vector<LiteralDegType> variants;
    for (const LiteralDegType &literal : POSSIBLE_LITERALS)
    {
        // (2,1)-типы доступны через sv, но по умолчанию выключены.
        if (literal.i != 2 || literal.j != 1)
            variants.push_back(literal);
    }

    FrontierOwner owner;
    vector<CNF *> cur = {new CNF()};
    owner.adopt(cur);
    bool root_initialized = false;

    vector<int> ids;
    vector<string> vars;

    string command;

    print_help_universal();

    // double C = 1.28855;
    double C = 1.2873;

    while (command != "exit")
    {
        cout << "Введите команду: ";
        owner.retain(cur);
        if (!(cin >> command)) break;

        if (command == "add")
        {
            string var_name;
            int i, j;
            string type;

            read_arguments(var_name, i, j, type);

            if (root_initialized)
                throw invalid_argument("add can only initialize the root; use addpos");
            if (type != "SINGLETON" && type != "ANY" && type != "a")
                throw invalid_argument("expected SINGLETON or ANY");
            LitType new_type = type == "SINGLETON" ? SINGLETON : ANY;
            validate_degree(i, j, new_type);

            if (VAR2ID.count(var_name) != 0)
            {
                cout << "Это имя переменной уже занято. Попробуйте другое название переменной\n";
                continue;
            }

            Literal new_lit = Literal(var_name);
            ids.push_back(new_lit.id);
            vars.push_back(var_name);

            cout << "Добавляем переменную " << var_name << " вида (" << i << ", " << j << ")" << (new_type == SINGLETON ? "-singleton" : "") << endl;

            vector<CNF *> new_lit_variants;

            for (CNF *cnf : cur)
            {
                auto new_vars = add_new_var(cnf, var_name, i, j, new_type);
                owner.adopt(new_vars);
                root_initialized = true;
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "addlit")
        {
            int i, j;
            string type;
            read_arguments(i, j, type);

            if (i < 1 || j < 1 || (type != "SINGLETON" && type != "ANY"))
            {
                cout << "Ожидается: addlit [i >= 1] [j >= 1] [SINGLETON | ANY]\n\n";
                continue;
            }

            LiteralDegType literal = {i, j, type == "SINGLETON" ? SINGLETON : ANY};
            validate_degree(i, j, literal.type);
            auto same_literal = [&](const LiteralDegType &other) {
                return other.i == literal.i && other.j == literal.j &&
                       other.type == literal.type;
            };

            if (find_if(POSSIBLE_LITERALS.begin(), POSSIBLE_LITERALS.end(), same_literal) ==
                POSSIBLE_LITERALS.end())
                POSSIBLE_LITERALS.push_back(literal);

            if (find_if(variants.begin(), variants.end(), same_literal) == variants.end())
                variants.push_back(literal);

            cout << "Добавлен тип (" << i << ", " << j << ")-"
                 << (literal.type == SINGLETON ? "singleton" : "any") << "\n\n";
            continue;
        }

        if (command == "addpos")
        {
            if (!root_initialized) throw invalid_argument("initialize the root with add first");
            string var_name;
            read_arguments(var_name);

            if (VAR2ID.count(var_name) != 0)
            {
                cout << "Это имя переменной уже занято. Попробуйте другое название переменной\n";
                continue;
            }

            Literal new_lit = Literal(var_name);
            ids.push_back(new_lit.id);
            vars.push_back(var_name);

            string l;

            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            read_command_line(l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            auto _posfunc = create_pos_func(need_lits, no_lits);

            vector<CNF *> new_lit_variants;

            for (CNF *cnf : cur)
            {
                auto new_vars = add_new_var_in_place(cnf, var_name, _posfunc, variants);
                owner.adopt(new_vars);
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "set")
        {
            read_arguments(C);
            if (!isfinite(C) || C <= 1) throw invalid_argument("target must exceed 1");

            cout << "C = " << C << "\n\n";

            continue;
        }

        if (command == "assumptions")
        {
            string value;
            read_arguments(value);
            if (value != "on" && value != "off")
            {
                cout << "Ожидается assumptions on или assumptions off\n\n";
                continue;
            }
            MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS = value == "on";
            cout << "Named assumptions: "
                 << (MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS ? "ON" : "OFF")
                 << "\n\n";
            continue;
        }

        if (command == "sv")
        {
            cout << "Введите булеву маску возможных литералов для добавления в следующем порядке (0 - не добавлять / 1 - добавить):\n";
            vector <LiteralDegType> new_pos_literals;
            const vector<LiteralDegType> &tmplte = POSSIBLE_LITERALS;

            for(LiteralDegType dt : tmplte)
            {
                cout << dt.i << " " << dt.j << " ";
                if (dt.type == LitType::SINGLETON)
                {
                    cout << "SINGLETON";
                }
                else if (dt.type == LitType::ANY)
                {
                    cout << "ANY";
                }
                cout << endl;
            }

            string msk;
            read_arguments(msk);

            if (msk.size() != tmplte.size() ||
                msk.find_first_not_of("01") != string::npos)
            {
                cout << "Ожидается маска из " << tmplte.size()
                     << " символов 0/1; список не изменён.\n\n";
                continue;
            }

            for(size_t i = 0; i < msk.size(); ++i)
            {
                if(msk[i] == '1')
                    new_pos_literals.push_back(tmplte[i]);
            }

            swap(new_pos_literals, variants);

            cout << "Сейчас в рассмотрении:\n";
            for(LiteralDegType lt : variants)
            {
                cout << "(" << lt.i << ", " << lt.j << ")";
                if(lt.type == SINGLETON)
                {
                    cout << "-singleton";
                }
                cout << endl;
            }
            continue;
        }   

        if (command == "setposfunc")
        {
            string l;

            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            read_command_line(l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token.empty()) continue;
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(intern_literal(Literal(token.substr(1)).id, true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(intern_literal(Literal(token).id, false));
                }
            }
            cout << endl;

            posfunc = create_pos_func(need_lits, no_lits);
            continue;
        }

        if (command == "simple_branch")
        {
            branch_epoch_universal(cur, ids, C, false);
            cout << endl;
            continue;
        }

        if (command == "branch")
        {
            branch_epoch_universal(cur, ids, C, true);
            cout << endl;
            continue;
        }

        if (command == "head")
        {
            int n;
            read_arguments(n);

            for (int i = 0; i < min((int)cur.size(), n); ++i)
            {
                print_cnf(*cur[i]);
                cout << endl;
            }

            continue;
        }

        if (command == "print")
        {
            int i;
            read_arguments(i);

            if (i < 0 || i >= (int)cur.size())
            {
                cout << "Формулы с индексом " << i
                     << " сейчас нет; осталось [" << cur.size()
                     << "] вариантов.\n\n";
                continue;
            }

            pretty_branch_print(vars, cur.at(i));
            cout << endl;

            ProofNode reg_node = cur.at(i)->branch(ids);
            ProofNode group_node = cur.at(i)->branch_group(ids, -1, false, C);

            vector<int> reg_branch = reg_node.vec;
            vector<int> group_branch = group_node.vec;

            cout << "Regular Branch:\n";
            for (int r : reg_branch)
                cout << r << " ";

            cout << "\n|  " << branching_factor(reg_branch);
            cout << endl;

            cout << "Group Branch:\n";
            for (int r : group_branch)
                cout << r << " ";
            cout << "\n|  " << branching_factor(group_branch);
            cout << "\n\n";

            cout << "Pos Func:\t";
            cout << posfunc(cur.at(i)) << "\n\n";

            continue;
        }

        if (command == "printall")
        {
            for (int i = 0; i < cur.size(); ++i)
            {
                pretty_branch_print(vars, cur.at(i));
                cout << endl;

                ProofNode group_node = cur.at(i)->branch_group(ids, -1, false, C);

                vector<int> group_branch = group_node.vec;

                cout << "Group Branch:\n";
                for (int r : group_branch)
                    cout << r << " ";
                cout << "\n|  " << branching_factor(group_branch);
                cout << "\n\n";

                cout << "=================================================\n\n";

            }

            continue;
        }


        if (command == "printworst")
        {
            long double worst = -1;
            int worst_ind = -1;
            for (int i = 0; i < cur.size(); ++i)
            {
                long double gfactor = branching_weight(cur.at(i)->branch_group(ids, -1, false, C).vec, C);
                
                if (gfactor > worst)
                {
                    worst = gfactor;
                    worst_ind = i;
                }
            }

            cout << "Formula: " << worst_ind << '\n';
            cout << "| W_q = " << worst << "\n\n";

            continue;
        }

        if (command == "stats")
        {
            if (cur.empty())
            {
                cout << "В данный момент нет вариантов для анализа.\n\n";
                continue;
            }

            double min_bf = 1e18; // Достаточно большое число для инициализации минимума
            double max_bf = -1.0;

            // vector <int> mn_branch;
            // vector <int> mx_branch;

            for (CNF *cnf : cur)
            {

                double current_bf = cnf->branch_group(ids, -1, false, C).tau;

                min_bf = min(min_bf, current_bf);
                max_bf = max(max_bf, current_bf);
            }

            cout << "Статистика по " << cur.size() << " вариантам:\n";
            cout << "Минимальный Branching Factor:  " << min_bf << "\n";
            cout << "Максимальный Branching Factor: " << max_bf << "\n\n";

            continue;
        }

        if (command == "empty_divide")
        {
            int i;
            read_arguments(i);

            if (i == -1)
            {
                vector<CNF *> next_cur;
                int success_count = 0;
                
                for (CNF *cnf : cur)
                {
                    DivideResult res = empty_divide(cnf, C);
                    if (res.cnf_empty != nullptr)
                    {
                        owner.adopt({res.cnf_empty, res.cnf_not_empty});
                        next_cur.push_back(res.cnf_empty);
                        next_cur.push_back(res.cnf_not_empty);
                        success_count++;
                    }
                    else
                    {
                        next_cur.push_back(cnf);
                    }
                }
                swap(cur, next_cur);
                cout << "empty_divide успешно применен к " << success_count << " формулам.\n";
                cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
            }
            else
            {
                cout << "Извините, пока что empty_divide работает только с -1\n\n";
                // if (i >= 0 && i < (int)cur.size())
                // {
                //     pair<CNF *, CNF *> res = empty_divide(cur[i]);
                //     if (res.first != nullptr)
                //     {
                //         // Удаляем старую формулу и на её место вставляем две новые
                //         CNF* old_cnf = cur[i];
                //         cur.erase(cur.begin() + i);
                //         cur.insert(cur.begin() + i, res.second);
                //         cur.insert(cur.begin() + i, res.first);
                //         // delete old_cnf; // Не забывайте про освобождение памяти

                //         cout << "empty_divide успешно применен к формуле " << i << ".\n";
                //         cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
                //     }
                //     else
                //     {
                //         cout << "В формуле " << i << " не найдено литералов '?' для разбиения.\n\n";
                //     }
                // }
                // else
                // {
                //     cout << "Неверный индекс формулы.\n\n";
                // }
            }
            continue;
        }

        if (command == "factor")
        {
            std::string l;
            read_command_line(l);
            read_command_line(l);

            stringstream ss(l);
            string token;

            vector<int> C_branch;

            while (getline(ss, token, ' '))
            {
                if (!token.empty()) C_branch.push_back(stoi(token));
            }
            cout << endl;

            cout << setprecision(10) << branching_factor(C_branch) << endl;

            continue;
        }

        if (command == "target")
        {
            int i;
            read_arguments(i);

            cur = {cur.at(i)};
            cout << "\n\n";
            continue;
        }

        if (command == "drop")
        {
            int i;
            read_arguments(i);

            if (i < 0 || i >= (int)cur.size()) throw out_of_range("drop index out of range");
            cur.erase(cur.begin() + i);
            
            cout << "Done.\n\n";
            continue;
        }

        if (command == "help")
        {
            print_help_universal();
            continue;
        }

        if (command == "exit")
        {
            break;
        }

        cout << "Команда [" << command << "] не распознана\n";
    }
}
