#include "cnf.h"
#include "test.h"
#include "cert_logger.h"
#include "lemmas.h"
#include "node_worker.h"

#include <iostream>
#include <functional>
#include <cmath>

using namespace std;

map<string, function<void()>> test_names;

void print_help()
{
    cout << "Usage:\n";
    cout << "./maxsat_prover [test_name]\n\n";
    cout << "./maxsat_prover --save-lemma Q FILE test  (fixed-q session; export during assembly)\n\n";
    cout << "./maxsat_prover --lemma FILE [--lemma FILE ...] test\n\n";
    cout << "./maxsat_prover node-worker  (global_search versioned stdin protocol; JSON stdout)\n\n";
    cout << "--allow-restarts  Enable checked variable-eliminating global restarts (local induction steps)\n\n";
    cout << "Available tests:\n";
    cout << "basic\tBasic clauses\n";
    cout << "2branch\tTests all variants with 2 vars (x, y) (3,2)-literals\n";
    cout << "3branch\tTests all variants with 3 vars (x, y, z) (3,2)-literals\n";
    cout << "factor\tTests factor branch computing\n";
    cout << "weight\tCheck fixed-target strategy selection\n";
    cout << "cache\tCheck residual formula caching\n";
    cout << "cover\tCheck substitution groups and weighted covers\n";
    cout << "absorption\tCheck compensated assignment dominance\n";
    cout << "lemmas\tCheck proof-backed local lemmas\n";
    cout << "saved_lemmas\tExercise loaded template matches and cache policy\n";
    cout << "subset\tInteractive test for subset func\n";
    cout << "addvar\tTest add_new_var func\n";
    cout << "nounknown\tTest no unknown literals\n";
    cout << "test\tInteractive test for branching etc.\n";
    cout << "reductions\tCheck constructive reductions\n";
    cout << "groups3\tCheck precomputed groups\n";
    cout << "safety\tCheck bounds and exposure preconditions\n";
}

void fill_test_names()
{
    test_names["basic"] = test_basics;
    test_names["2branch"] = test_branch_two_vars;
    test_names["3branch"] = test_branch_three_vars;
    test_names["factor"] = test_branching_factor;
    test_names["weight"] = test_weighted_search;
    test_names["cache"] = test_strategy_cache;
    test_names["cover"] = test_group_cover;
    test_names["absorption"] = test_compensated_absorption;
    test_names["lemmas"] = test_proved_lemmas;
    test_names["saved_lemmas"] = test_saved_lemmas;
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

    string test_name;
    vector<string> lemma_files;
    bool allow_restarts=false;
    try
    {
        for (int index = 1; index < argc; ++index)
        {
            string argument = argv[index];
            if (argument == "--save-lemma")
            {
                if (lemma_export_enabled() || index + 2 >= argc)
                    throw invalid_argument("expected --save-lemma Q FILE exactly once");
                lemma_export_settings.target = argv[++index];
                size_t consumed = 0;
                lemma_export_settings.q = stod(lemma_export_settings.target, &consumed);
                if (consumed != lemma_export_settings.target.size() ||
                    lemma_export_settings.target.find_first_not_of("0123456789.+-eE") != string::npos ||
                    !isfinite(lemma_export_settings.q) || lemma_export_settings.q <= 1)
                    throw invalid_argument("lemma target must be a finite decimal greater than one");
                lemma_export_settings.output_file = argv[++index];
                if (lemma_export_settings.output_file.empty())
                    throw invalid_argument("lemma output filename must not be empty");
            }
            else if (argument == "--allow-restarts") allow_restarts=true;
            else if (argument == "--lemma")
            {
                if (index + 1 >= argc) throw invalid_argument("expected --lemma FILE");
                lemma_files.push_back(argv[++index]);
            }
            else if (test_name.empty()) test_name = argument;
            else throw invalid_argument("unexpected argument: " + argument);
        }
        if (allow_restarts && lemma_export_enabled())
            throw invalid_argument("restart induction steps cannot yet be exported as ordinary saved lemmas");
        if (lemma_export_enabled() && test_name != "test")
            throw invalid_argument("--save-lemma is only available for interactive sessions (test)");
    }
    catch (const std::exception &error)
    {
        cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
    if (test_name.empty()) { print_help(); return 0; }
    if (test_name == "node-worker") {
        if (lemma_export_enabled() || allow_restarts) {
            cerr << "ERROR: node-worker settings belong in its stdin request\n";
            return 1;
        }
        return run_node_worker(lemma_files);
    }

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
        MaxSATSettings.ALLOW_POLYNOMIAL_RESTARTS=allow_restarts;
        load_saved_lemmas(lemma_files);
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
