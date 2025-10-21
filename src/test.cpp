#include "cnf.h"
#include <assert.h>
#include <iostream>

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

    for (int i = 0; i < with_z.size(); ++i)
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

    for (int i = 0; i < with_y.size(); ++i)
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
    Literal x = Literal("x");
    Literal y = Literal("y");
    Literal z = Literal("z");

    Literal nx = x.neg();
    Literal ny = y.neg();
    Literal nz = z.neg();

    auto v1 = (vector<Literal *>){&UNKNOWN_LITERAL, &x, &y, &z};
    auto v2 = (vector<Literal *>){&UNKNOWN_LITERAL, &x};
    auto v3 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx, &y, &z};
    auto v4 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx};
    auto v5 = (vector<Literal *>){&UNKNOWN_LITERAL, &nx};
    auto v6 = (vector<Literal *>){&UNKNOWN_LITERAL, &y, &nz};
    auto v7 = (vector<Literal *>){&UNKNOWN_LITERAL, &ny, &nz};
    auto v8 = (vector<Literal *>){&UNKNOWN_LITERAL, &ny, &z};

    Clause c1 = Clause(v1);
    Clause c2 = Clause(v2);
    Clause c3 = Clause(v3);
    Clause c4 = Clause(v4);
    Clause c5 = Clause(v5);
    Clause c6 = Clause(v6);
    Clause c7 = Clause(v7);
    Clause c8 = Clause(v8);

    vector<Clause *> clause_vec = {&c1, &c2, &c3, &c4, &c5, &c6, &c7, &c8};

    CNF cnf(clause_vec);

    print_cnf(cnf);

    vector <int> reg_branch = cnf.branch({x.id, y.id, z.id});
    vector <int> group_branch = cnf.branch_group({x.id, y.id, z.id});

    cout << "Regular Branch:\n";
    for (int r : reg_branch)
        cout << r << " ";
    cout << endl;

    cout << "Group Branch:\n";
    for (int r : group_branch)
        cout << r << " ";
    cout << endl;
    
}