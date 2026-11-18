#include "cnf.h"
#include "test.h"
#include "cert_logger.h"

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
    cout << "factor\tTests factor branch computing\n";
    cout << "weight\tCheck fixed-target strategy selection\n";
    cout << "step51\tCheck constructive Step 5.1 in both polarities\n";
    cout << "cache\tCheck residual formula caching\n";
    cout << "cover\tCheck substitution groups and weighted covers\n";
    cout << "subset\tInteractive test for subset func\n";
    cout << "addvar\tTest add_new_var func\n";
    cout << "nounknown\tTest no unknown literals\n";
    cout << "test\tInteractive test for branching etc.\n";
    cout << "reductions\tCheck constructive reductions\n";
    cout << "safety\tCheck bounds and exposure preconditions\n";
}

void fill_test_names()
{
    test_names["basic"] = test_basics;
    test_names["factor"] = test_branching_factor;
    test_names["weight"] = test_weighted_search;
    test_names["step51"] = test_step51;
    test_names["cache"] = test_strategy_cache;
    test_names["cover"] = test_group_cover;
    test_names["subset"] = test_subset_func;
    test_names["addvar"] = test_add_new_var;
    test_names["nounknown"] = test_no_unknown_literal;
    test_names["test"] = test_universal;
    test_names["reductions"] = test_constructive_reductions;
    test_names["safety"] = test_safety;

    test_names["help"] = print_help;
    test_names["--help"] = print_help;

}

int main(int argc, const char *argv[])
{
    fill_test_names();

    if (argc != 2)
    {
        print_help();
        return argc == 1 ? 0 : 1;
    }

    string test_name = argv[1];

    if (test_names.count(test_name) == 0)
    {
        print_help();
        return 1;
    }

    if (test_name == "help" || test_name == "--help")
    {
        print_help();
        return 0;
    }
    try
    {
        preprocess();
        if (test_name == "test") global_logger.init("pre_certificate.jsonl");
        test_names[test_name]();
        global_logger.close();
    }
    catch (const std::exception &error)
    {
        global_logger.close();
        cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
