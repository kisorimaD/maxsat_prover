#include "cnf.h"
#include "test.h"
#include <assert.h>
#include <iostream>
#include <sstream>
#include <functional>

using namespace std;

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

void test_branching_factor()
{
    cout << branching_factor({6, 6, 5, 5}) << endl;
    cout << branching_factor({1, 2}) << endl;
    cout << branching_factor({4}) << endl;
}

void test_branch_three_vars()
{
    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    print_cnf(*with_x);

    cout << "Добавляем переменную y (2, 3)-литерал\n";

    vector<CNF *> with_y = add_new_var(with_x, "y", 3, 2, ANY);

    vector<CNF *> with_z;

    cout << "Получили " << with_y.size() << " вариантов" << endl;

    cout << "Добавляем z (2, 3)" << endl;

    for (CNF *br : with_y)
    {
        auto new_vars = add_new_var(br, "z", 3, 2, ANY);

        with_z.resize(with_z.size() + new_vars.size());
        copy(new_vars.begin(), new_vars.end(), with_z.rbegin());
    }

    cout << "Итого без эвристик и группировок получили " << with_z.size() << " вариантов" << endl;

    cout << "\n\n============[ Начинаем бренчинг по этим вариантам ]==============\n";

    double mx_factor = 0;
    CNF *mx_cnf = nullptr;
    vector<int> mx_branch;

    Literal x = Literal("x");
    Literal y = Literal("y");
    Literal z = Literal("z");

    for (int i = 0; i < (int)with_z.size(); ++i)
    {
        cout << "Выполняется " << i << "/" << with_z.size() << "                \r";

        vector<int> branch = with_z[i]->branch({x.id, y.id, z.id});

        double factor = branching_factor(branch);

        if (factor > mx_factor)
        {
            mx_factor = factor;
            mx_cnf = with_z[i];
            mx_branch = branch;
        }
    }

    cout << "======================[ Перебор завершен ]=======================\n\n";

    if (mx_factor == 0)
    {
        cout << "ERROR\n";
        return;
    }

    cout << "Худший вариант:\n";
    print_cnf(*mx_cnf);
    cout << "\nBranch: ";
    for (int b : mx_branch)
    {
        cout << b << " ";
    }
    cout << "\nBranching Factor: " << mx_factor << endl;
}

void test_branch_two_vars()
{
    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    print_cnf(*with_x);

    cout << "Добавляем переменную y (4, 1)-singleton-литерал\n";

    // vector<CNF *> with_y = add_new_var(with_x, "y", 4, 1, SINGLETON);
    vector<CNF *> with_y = add_new_var(with_x, "y", 3, 2, ANY);

    cout << "Получили " << with_y.size() << " вариантов" << endl;

    cout << "\n\n============[ Начинаем бренчинг по этим вариантам ]==============\n";

    double mx_factor = 0;
    CNF *mx_cnf = nullptr;
    vector<int> mx_branch;

    Literal x = Literal("x");
    Literal y = Literal("y");

    for (int i = 0; i < (int)with_y.size(); ++i)
    {
        cout << "Выполняется " << i << "/" << with_y.size() << "                \r";

        vector<int> branch = with_y[i]->branch({x.id, y.id});

        double factor = branching_factor(branch);

        if (factor > mx_factor)
        {
            mx_factor = factor;
            mx_cnf = with_y[i];
            mx_branch = branch;
        }
    }

    cout << "======================[ Перебор завершен ]=======================\n\n";

    if (mx_factor == 0)
    {
        cout << "ERROR\n";
        return;
    }

    cout << "Худший вариант:\n";
    print_cnf(*mx_cnf);
    cout << "\nBranch: ";
    for (int b : mx_branch)
    {
        cout << b << " ";
    }
    cout << "\nBranching Factor: " << mx_factor << endl;
}

void test_subset_func()
{
    while (true)
    {
        int A, B;
        cin >> A;

        if (A == -1)
            break;

        cin >> B;

        cout << (is_A_subset_of_B(A, B) ? "YES\n" : "NO\n");
    }
}

void test_add_new_var()
{
    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);
    cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    print_cnf(*with_x);

    cout << "Добавляем переменную y (3, 2)-литерал\n";

    vector<CNF *> with_y = add_new_var(with_x, "y", 3, 2, ANY);

    cout << "Размер " << with_y.size() << endl;
    for (int i = 0; i < 10; ++i)
    {
        print_cnf(*with_y[i]);
    }
}

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

void test_no_unknown_literal()
{

    CNF cnf;

    CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);

    cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    print_cnf(*with_x);

    cout << "Добавляем переменную y (3, 2)-литерал\n";

    vector<CNF *> with_y = add_new_var(with_x, "y", 4, 1, SINGLETON);

    cout << "Размер: " << with_y.size() << endl;

    cout << "Введите номер клозы для проверки разбора. -1 для окончания теста\n";

    int k;
    cin >> k;

    vector<string> vars = {"x", "y"};

    Literal x = Literal("x");
    Literal y = Literal("y");

    while (k != -1)
    {
        pretty_branch_print(vars, with_y.at(k));

        vector<int> reg_branch = with_y.at(k)->branch({x.id, y.id});
        vector<int> group_branch = with_y.at(k)->branch_group({x.id, y.id});

        cout << "Regular Branch:\n";
        for (int r : reg_branch)
            cout << r << " ";
        cout << endl;

        cout << "Group Branch:\n";
        for (int r : group_branch)
            cout << r << " ";
        cout << endl;

        cin >> k;
    }
}

function<int(CNF *)> create_pos_func(set<Literal *, LiteralPtrLess> need_lits, set<Literal *, LiteralPtrLess> no_lits)
{
    return [need_lits, no_lits](CNF *cnf)
    {
        for (int i = 0; i < cnf->clauses.size(); ++i)
        {
            Clause *now_clause = cnf->clauses[i];

            if(now_clause->lits.find(&UNKNOWN_LITERAL) == now_clause->lits.end())
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

        return 0;
    };
}

void printProgress_test(double percentage)
{
    int pb_length = 60;
    int val = static_cast<int>(percentage * 100);
    int lpad = static_cast<int>(percentage * pb_length);
    int rpad = pb_length - lpad;
    std::cout << "\r" << val << "% [" << std::string(lpad, '#') << std::string(rpad, '-') << "]" << std::flush;
}

void branch_epoch_universal(vector<CNF *> &variants, vector<int> &ids, double C, bool is_group_branch, bool is_xiao_branch, int xiao_depth = 1)
{
    cout << "Начинается примитивная фильтрация\n";
    vector<CNF *> filtered_variants;

    for (CNF *cnf : variants)
    {
        vector<int> naive_branch = cnf->branch(ids);
        double bf = branching_factor(naive_branch);

        if (bf >= C)
        {
            filtered_variants.push_back(cnf);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    if(is_xiao_branch)
    {
        cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с Reduction Rules\n";

        swap(filtered_variants, variants);
        filtered_variants.clear();

        for(CNF *cnf : variants)
        {
            vector <int> rrbranch = cnf->xiao_branch(xiao_depth);
            double bf = branching_factor(rrbranch);

            if (bf >= C)
            {
                filtered_variants.push_back(cnf);
            }
        }
        
        cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";
        
        cout << "Осталось [" << filtered_variants.size() << "]\n\n";

    }


    if (!is_group_branch)
    {
        swap(filtered_variants, variants);
        return;
    }

    cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с группировкой\n";

    bool need_pb = false;
    if ((filtered_variants.size() << (2 * ids.size())) > 1000)
    {
        need_pb = true;
        cout << "\nWARNING! Слишком большой размер оставшегося массива, бренчинг с группировкой может работать очень медленно.\n\n";
    }

    swap(variants, filtered_variants);
    filtered_variants.clear();

    if (need_pb)
        progress_counter_test = 0;

    int vsize = variants.size();

    for (CNF *cnf : variants)
    {
        // try k = ids.size()
        // vector<int> approx_group_branch = cnf->branch_group(ids, ids.size());
        // double small_try_bf = branching_factor(approx_group_branch);

        // if (small_try_bf >= C)
        // {
        //     vector<int> group_branch = cnf->branch_group(ids, -1);
        //     double bf = branching_factor(group_branch);

        //     if (bf >= C)
        //     {
        //         filtered_variants.push_back(cnf);
        //     }
        // }

        bool flag = false;
        for (int k = 2; k <= ids.size(); ++k)
        {
            vector<int> approx_group_branch = cnf->branch_group(ids, k);
            double small_try_bf = branching_factor(approx_group_branch);

            if (small_try_bf < C)
            {
                flag = true;
                break;
            }
        }

        if (!flag)
        {
            // filtered_variants.push_back(cnf);
            vector<int> group_branch = cnf->branch_group(ids, -1);
            double bf = branching_factor(group_branch);

            if (bf >= C)
            {
                filtered_variants.push_back(cnf);
            }
        }

        if (need_pb)
            progress_counter_test++;

        if (need_pb && progress_counter_test % 5 == 0)
        {
            printProgress_test((double)progress_counter_test / vsize);
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
    cout << "   add [var_name] [i] [j] [SINGLETON | ANY]\t\tДобавить переменную (i, j), если SINGLETON, то синглтон\n";
    cout << "   addpos [var_name] [need_names] [no_names]\t\tДобавить новую переменную в первую клозу, в которой есть все\n\t\t\t\t\t\t\tпеременные из need_names и нет ни одной из no_names. Ввод разделяется строчками\n";
    cout << "   sv [mask]                               \t\tУстановить возможные типы литералов по битовой маске длины 9\n";
    cout << "   set [branching factor]                  \t\tУстановить порог С (по умолчанию равен 1.28854 или [6 6 5 5])\n";
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
void test_universal()
{
    progress_counter_test = 0;

    auto posfunc = create_pos_func(set<Literal *, LiteralPtrLess>(), set<Literal *, LiteralPtrLess>());

    vector<LiteralDegType> variants = POSSIBLE_LITERALS;

    CNF cnf;

    vector<CNF *> cur = {&cnf};

    vector<int> ids;
    vector<string> vars;

    string command;

    print_help_universal();

    // double C = 1.28855;
    double C = 1.2873;

    while (command != "exit")
    {
        cout << "Введите команду: ";
        cin >> command;

        if (command == "add")
        {
            string var_name;
            int i, j;
            string type;

            cin >> var_name >> i >> j >> type;

            LitType new_type = type == "SINGLETON" ? SINGLETON : ANY;

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
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "addpos")
        {
            string var_name;
            cin >> var_name;

            if (VAR2ID.count(var_name) != 0)
            {
                cout << "Это имя переменной уже занято. Попробуйте другое название переменной\n";
                continue;
            }

            Literal new_lit = Literal(var_name);
            ids.push_back(new_lit.id);
            vars.push_back(var_name);

            string l;

            getline(cin, l);
            getline(cin, l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(new Literal(token.substr(1), true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(new Literal(token));
                }
            }
            cout << endl;

            getline(cin, l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(new Literal(token.substr(1), true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(new Literal(token));
                }
            }
            cout << endl;

            auto _posfunc = create_pos_func(need_lits, no_lits);

            vector<CNF *> new_lit_variants;

            for (CNF *cnf : cur)
            {
                auto new_vars = add_new_var_in_place(cnf, var_name, _posfunc, variants);
                new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
                copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
            }

            swap(cur, new_lit_variants);

            cout << "В текущем рассмотрении [" << cur.size() << "] вариантов\n\n";

            continue;
        }

        if (command == "set")
        {
            cin >> C;

            cout << "C = " << C << "\n\n";

            continue;
        }

        if (command == "sv")
        {
            cout << "Введите булеву маску возможных литералов для добавления в следующем порядке (0 - не добавлять / 1 - добавить):\n";
            // cout << "{1, 3, ANY}\n{3, 1, ANY}\n{2, 2, ANY}\n{3, 2, ANY}\n{2, 3, ANY}\n{1, 4, ANY}\n{4, 1, ANY}\n{3, 1, SINGLETON}\n{4, 1, SINGLETON}}\n\n";
            

            vector <LiteralDegType> new_pos_literals;
            
            vector <LiteralDegType> tmplte = {
            {1, 3, SINGLETON},
            {3, 1, SINGLETON},
            {2, 2, ANY},
            {3, 2, ANY},
            {2, 3, ANY},
            {3, 1, SINGLETON},
            {4, 1, SINGLETON}};

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
            cin >> msk;

            for(int i = 0; i < msk.size(); ++i)
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

            getline(cin, l);
            getline(cin, l);

            stringstream ss(l);
            string token;

            set<Literal *, LiteralPtrLess> need_lits;

            cout << "NEED_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                // need_names.push_back(token);
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    need_lits.insert(new Literal(token.substr(1), true));
                }
                else
                {
                    cout << token << " ";
                    need_lits.insert(new Literal(token));
                }
            }
            cout << endl;

            getline(cin, l);
            ss = stringstream(l);

            set<Literal *, LiteralPtrLess> no_lits;

            cout << "NO_NAMES:\t";
            while (getline(ss, token, ' '))
            {
                if (token[0] == '-')
                {
                    cout << "¬" << token.substr(1) << " ";
                    no_lits.insert(new Literal(token.substr(1), true));
                }
                else
                {
                    cout << token << " ";
                    no_lits.insert(new Literal(token));
                }
            }
            cout << endl;

            posfunc = create_pos_func(need_lits, no_lits);
            continue;
        }

        if (command == "simple_branch")
        {
            branch_epoch_universal(cur, ids, C, false, false);
            cout << endl;
            continue;
        }

        if (command == "xiao_branch")
        {
            int depth;

            cin >> depth;

            branch_epoch_universal(cur, ids, C, false, true, depth);
            cout << endl;
            continue;
        }

        if (command == "branch")
        {
            branch_epoch_universal(cur, ids, C, true, false);
            cout << endl;
            continue;
        }

        if (command == "head")
        {
            int n;
            cin >> n;

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
            cin >> i;

            pretty_branch_print(vars, cur.at(i));
            cout << endl;

            vector<int> reg_branch = cur.at(i)->branch(ids);
            vector<int> group_branch = cur.at(i)->branch_group(ids);
            vector<int> xiao_branch = cur.at(i)->xiao_branch(1);

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


            cout << "Xiao Branch (Depth = 1):\n";
            for (int r : xiao_branch)
                cout << r << " ";
            cout << "\n| " << branching_factor(xiao_branch);
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

                vector<int> reg_branch = cur.at(i)->branch(ids);
                vector<int> group_branch = cur.at(i)->branch_group(ids);
                vector<int> xiao_branch = cur.at(i)->xiao_branch(1);

                cout << "Group Branch:\n";
                for (int r : group_branch)
                    cout << r << " ";
                cout << "\n|  " << branching_factor(group_branch);
                cout << "\n\n";

                cout << "Xiao Branch (Depth = 1):\n";
                for (int r : xiao_branch)
                    cout << r << " ";
                cout << "\n| " << branching_factor(xiao_branch);
                cout << "\n\n";
                
                cout << "=================================================\n\n";

            }

            continue;
        }


        if (command == "printworst")
        {
            double worst = -1;
            int worst_ind = -1;
            for (int i = 0; i < cur.size(); ++i)
            {
                vector<int> group_branch = cur.at(i)->branch_group(ids);

                double gfactor = branching_factor(group_branch);
                
                if (gfactor > worst)
                {
                    worst = gfactor;
                    worst_ind = i;
                }
            }

            cout << "Formula: " << worst_ind << '\n';
            cout << "| " << worst << "\n\n";

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
                vector<int> group_branch = cnf->branch_group(ids);
                vector<int> xiao_branch = cnf->xiao_branch(1);

                double gfactor = branching_factor(group_branch);
                double xfactor = branching_factor(xiao_branch);

                // Берем минимум между групповым ветвлением и ветвлением xiao
                double current_bf = min(gfactor, xfactor);

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
            cin >> i;

            if (i == -1)
            {
                vector<CNF *> next_cur;
                int success_count = 0;
                
                for (CNF *cnf : cur)
                {
                    pair<CNF *, CNF *> res = empty_divide(cnf);
                    if (res.first != nullptr)
                    {
                        next_cur.push_back(res.first);
                        next_cur.push_back(res.second);
                        success_count++;
                        // Утечки памяти: желательно сделать delete cnf;    
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
                if (i >= 0 && i < (int)cur.size())
                {
                    pair<CNF *, CNF *> res = empty_divide(cur[i]);
                    if (res.first != nullptr)
                    {
                        // Удаляем старую формулу и на её место вставляем две новые
                        CNF* old_cnf = cur[i];
                        cur.erase(cur.begin() + i);
                        cur.insert(cur.begin() + i, res.second);
                        cur.insert(cur.begin() + i, res.first);
                        // delete old_cnf; // Не забывайте про освобождение памяти

                        cout << "empty_divide успешно применен к формуле " << i << ".\n";
                        cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
                    }
                    else
                    {
                        cout << "В формуле " << i << " не найдено литералов '?' для разбиения.\n\n";
                    }
                }
                else
                {
                    cout << "Неверный индекс формулы.\n\n";
                }
            }
            continue;
        }

        if (command == "factor")
        {
            std::string l;
            getline(cin, l);
            getline(cin, l);

            stringstream ss(l);
            string token;

            vector<int> C_branch;

            while (getline(ss, token, ' '))
            {
                C_branch.push_back(stoi(token));
            }
            cout << endl;

            cout << branching_factor(C_branch) << endl;

            continue;
        }

        if (command == "target")
        {
            int i;
            cin >> i;

            cur = {cur.at(i)};
            cout << "\n\n";
            continue;
        }

        if (command == "drop")
        {
            int i;
            cin >> i;

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