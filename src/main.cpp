#include "cnf.h"
#include "test.h"
#include "cert_logger.h"

#include <charconv>
#include <iostream>
#include <functional>
#include <limits>
#include <stdexcept>

using namespace std;

map<string, function<void()>> test_names;

void print_help()
{
    cout << "Usage:\n";
    cout << "./maxsat_prover [--max-clause-size k] "
            "[--max-variable-occurrences s] [test_name]\n";
    cout << "  k, s: -1 for no limit, or an integer from 1 to "
         << numeric_limits<int>::max() - 1 << "\n\n";
    cout << "Available tests:\n";
    cout << "basic\tBasic clauses\n";
    cout << "2branch\tTests all variants with 2 vars (x, y) (3,2)-literals\n";
    cout << "3branch\tTests all variants with 3 vars (x, y, z) (3,2)-literals\n";
    cout << "factor\tTests factor branch computing\n";
    cout << "subset\tInteractive test for subset func\n";
    cout << "addvar\tTest add_new_var func\n";
    cout << "nounknown\tTest no unknown literals\n";
    cout << "test\tInteractive test for branching etc.\n";
    cout << "reductions\tCheck constructive reductions\n";
    cout << "groups3\tCheck precomputed groups\n";
    cout << "safety\tCheck bounds and exposure preconditions\n";
}

int parse_positive_limit(const string &flag, const string &value)
{
    int result = 0;
    const char *begin = value.data();
    const char *end = begin + value.size();
    auto parsed = from_chars(begin, end, result);
    if (value.empty() || parsed.ec != errc() || parsed.ptr != end)
        throw invalid_argument(flag + " requires an integer");
    if (result != -1 && result < 1)
        throw invalid_argument(flag + " must be -1 or at least 1");
    if (result == numeric_limits<int>::max())
        throw invalid_argument(flag + " is too large");
    return result;
}

void fill_test_names()
{
    test_names["basic"] = test_basics;
    test_names["2branch"] = test_branch_two_vars;
    test_names["3branch"] = test_branch_three_vars;
    test_names["factor"] = test_branching_factor;
    test_names["subset"] = test_subset_func;
    test_names["addvar"] = test_add_new_var;
    test_names["nounknown"] = test_no_unknown_literal;
    test_names["test"] = test_universal;
    test_names["groups3"] = test_groups3_validity;
    test_names["reductions"] = test_constructive_reductions;
    test_names["safety"] = test_safety;

    test_names["help"] = print_help;
    test_names["--help"] = print_help;

}

int main(int argc, const char *argv[])
{
    fill_test_names();

    if (argc == 1)
    {
        print_help();
        return 0;
    }
    try
    {
        string test_name;
        int maximum_clause_size = -1;
        int maximum_variable_occurrences = -1;
        bool has_maximum_clause_size = false;
        bool has_maximum_variable_occurrences = false;

        for (int i = 1; i < argc; ++i)
        {
            string argument = argv[i];
            if (argument == "--max-clause-size" ||
                argument == "--max-variable-occurrences")
            {
                bool &seen = argument == "--max-clause-size"
                                 ? has_maximum_clause_size
                                 : has_maximum_variable_occurrences;
                if (seen)
                    throw invalid_argument(argument + " specified more than once");
                if (++i == argc)
                    throw invalid_argument(argument + " requires a value");
                int value = parse_positive_limit(argument, argv[i]);
                if (argument == "--max-clause-size")
                    maximum_clause_size = value;
                else
                    maximum_variable_occurrences = value;
                seen = true;
            }
            else if (test_name.empty())
            {
                test_name = argument;
            }
            else
            {
                throw invalid_argument("expected exactly one test name");
            }
        }

        if (test_name.empty())
            throw invalid_argument("test name is required");
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

        preprocess(maximum_clause_size, maximum_variable_occurrences);
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
