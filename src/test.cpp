#include "cnf.h"
#include "test.h"
#include <assert.h>
#include <iostream>
#include <sstream>

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

void test_branch_group()
{
    // Literal x = Literal("x");
    // Literal y = Literal("y");
    // Literal z = Literal("z");

    // Literal nx = x.neg();
    // Literal ny = y.neg();
    // Literal nz = z.neg();

    // auto v1 = (vector<Literal *>){&UNKNOWN_LITERAL, &x, &y, &z};
    // auto v2 = (vector<Literal *>){&UNKNOWN_LITERAL, &x};
    // auto v3 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx, &y, &z};
    // auto v4 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx};
    // auto v5 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx};
    // auto v6 = (vector<Literal *>){&UNKNOWN_LITERAL, &y, &nz};
    // auto v7 = (vector<Literal *>){&UNKNOWN_LITERAL, &ny, &nz};
    // auto v8 = (vector<Literal *>){&UNKNOWN_LITERAL, &ny, &z};

    // Clause c1 = Clause(v1);
    // Clause c2 = Clause(v2);
    // Clause c3 = Clause(v3);
    // Clause c4 = Clause(v4);
    // Clause c5 = Clause(v5);
    // Clause c6 = Clause(v6);
    // Clause c7 = Clause(v7);
    // Clause c8 = Clause(v8);

    // vector<Clause *> clause_vec = {&c1, &c2, &c3, &c4, &c5, &c6, &c7, &c8};

    Literal x = Literal("x");
    Literal nx = x.neg();

    Literal y = Literal("y");
    Literal ny = y.neg();

    Literal z = Literal("z");
    Literal nz = z.neg();

    vector<Literal *> v0 = {&UNKNOWN_LITERAL, &x, &ny};
    vector<Literal *> v1 = {&UNKNOWN_LITERAL, &x, &y};
    vector<Literal *> v2 = {&UNKNOWN_LITERAL, &x, &y, &z};
    vector<Literal *> v3 = {&UNKNOWN_LITERAL, &nx, &ny};
    vector<Literal *> v4 = {&UNKNOWN_LITERAL, &nx, &y};
    vector<Literal *> v5 = {&UNKNOWN_LITERAL, &z};
    vector<Literal *> v6 = {&UNKNOWN_LITERAL, &z};
    vector<Literal *> v7 = {&UNKNOWN_LITERAL, &nz};
    vector<Literal *> v8 = {&UNKNOWN_LITERAL, &nz};

    Clause c0 = Clause(v0);
    Clause c1 = Clause(v1);
    Clause c2 = Clause(v2);
    Clause c3 = Clause(v3);
    Clause c4 = Clause(v4);
    Clause c5 = Clause(v5);
    Clause c6 = Clause(v6);
    Clause c7 = Clause(v7);
    Clause c8 = Clause(v8);

    vector<Clause *> clause_vec = {&c0, &c1, &c2, &c3, &c4, &c5, &c6, &c7, &c8};

    CNF cnf(clause_vec);

    print_cnf(cnf);

    vector<int> reg_branch = cnf.branch({x.id, y.id, z.id});
    vector<int> group_branch = cnf.branch_group({x.id, y.id, z.id});

    cout << "Regular Branch:\n";
    for (int r : reg_branch)
        cout << r << " ";
    cout << endl;

    cout << "Group Branch:\n";
    for (int r : group_branch)
        cout << r << " ";
    cout << endl;
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

    cout << "min F: " << cnf->min_F << endl;

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

    while(k != -1)
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


void printProgress_test(double percentage)
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

    if(!is_group_branch)
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
        vector<int> group_branch = cnf->branch_group(ids);
        double bf = branching_factor(group_branch);

        if (bf >= C)
        {
            filtered_variants.push_back(cnf);
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
}


void print_help_universal()
{
    cout << "Список команд:\n";
    cout << "   add [var_name] [i] [j] [SINGLETON | ANY]\t\tДобавить переменную (i, j), если SINGLETON, то синглтон\n";
    cout << "   set [branching factor]                  \t\tУстановить порог С (по умолчанию равен 1.28854 или [6 6 5 5])\n";
    cout << "   branch                                  \t\tОбычное отсеивание + с группировкой бренчингом всех вариантов ниже С\n";
    cout << "   simple_branch                           \t\tОбычное отсеивание без группировки бренчингом всех вариантов ниже С\n";
    cout << "   target [i]                              \t\tОставить в рассмотрении только [i] вариант\n";
    cout << "   head [n]                                \t\tВывести [n] первых вариантов сейчас\n";
    cout << "   print [i]                               \t\tВывести [i] вариант и разобрать по переменным\n";
    cout << "   factor [vector]                         \t\tВывести branching factor для заданного вектора\n";
    cout << "   help                                    \t\tВывести список команд (этот)\n";
    cout << "   exit                                    \t\tВыйти из тестирования\n\n";
}

void test_universal()
{
    progress_counter_test = 0;

    CNF cnf;

    vector <CNF *> cur = {&cnf};

    vector <int> ids;
    vector <string> vars;

    string command;

    print_help_universal();
    
    double C = 1.28855;

    while(command != "exit")
    {
        cout << "Введите команду: ";
        cin >> command;

        if(command == "add")
        {
            string var_name;
            int i, j;
            string type;

            cin >> var_name >> i >> j >> type;

            LitType new_type = type == "SINGLETON" ? SINGLETON : ANY;

            if(VAR2ID.count(var_name) != 0)
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

        if(command == "set")
        {
            cin >> C;

            cout << "C = " << C << "\n\n";

            continue;
        }


        if(command == "simple_branch")
        {
            branch_epoch_universal(cur, ids, C, false);
            cout << endl;
            continue;
        }


        if(command == "branch")
        {
            branch_epoch_universal(cur, ids, C, true);
            cout << endl;
            continue;
        }

        if(command == "head")
        {
            int n;
            cin >> n;

            for(int i = 0; i < min((int)cur.size(), n); ++i)
            {
                print_cnf(*cur[i]);
                cout << endl;
            }

            continue;
        }

        if(command == "print")
        {
            int i;
            cin >> i;

            pretty_branch_print(vars, cur.at(i));
            cout << endl;

            vector<int> reg_branch = cur.at(i)->branch(ids);
            vector<int> group_branch = cur.at(i)->branch_group(ids);

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

            continue;
        }

        if(command == "factor")
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

            cout <<  branching_factor(C_branch) << endl;

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

        if(command == "help")
        {
            print_help_universal();
            continue;
        }

        if(command == "exit")
        {
            break;
        }

        cout << "Команда [" << command << "] не распознана\n";
    }
}