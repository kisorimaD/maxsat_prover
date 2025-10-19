#include "cnf.h"
#include "test.h"
#include <iostream>
#include <functional>

using namespace std;

map<string, function<void()>> test_names;

void print_help()
{
    cout << "Usage:\n";
    cout << "./maxsat_prover [test_name]\n\n";
    cout << "Available tests:\n";
    cout << "basic\tBasic clauses\n";
    cout << "2branch\tTests all variants with 2 vars (x, y) (3,2)-literals\n";
    cout << "3branch\tTests all variants with 3 vars (x, y, z) (3,2)-literals\n";
    cout << "factor\tTests factor branch computing\n";
}

void fill_test_names()
{
    test_names["basic"] = test_basics;
    test_names["2branch"] = test_branch_two_vars;
    test_names["3branch"] = test_branch_three_vars;
    test_names["factor"] = test_branching_factor;
    test_names["help"] = print_help;
    test_names["--help"] = print_help;
}

int main(int argc, const char *argv[])
{
    preprocess();
    fill_test_names();

    if (argc != 2)
    {
        print_help();
        return 0;
    }

    string test_name = argv[1];

    if (test_names.count(test_name) == 0)
    {
        print_help();
    }

    test_names[test_name]();
}
