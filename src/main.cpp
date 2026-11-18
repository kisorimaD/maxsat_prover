#include "cert_logger.h"
#include "cli.h"
#include "cnf.h"

#include <iostream>
#include <string_view>

namespace {
void print_help()
{
    std::cout << "Usage: ./maxsat_prover interactive\n"
                 "Run the interactive search. Type help to list its commands.\n"
                 "Run make check for tests.\n";
}
}

int main(int argc, const char *argv[])
{
    if (argc == 1)
    {
        print_help();
        return 0;
    }

    if (argc != 2)
    {
        print_help();
        return 1;
    }

    std::string_view command = argv[1];
    if (command == "help" || command == "--help")
    {
        print_help();
        return 0;
    }
    if (command != "interactive")
    {
        print_help();
        return 1;
    }

    try
    {
        preprocess();
        global_logger.init("pre_certificate.jsonl");
        run_interactive();
        global_logger.close();
    }
    catch (const std::exception &error)
    {
        global_logger.close();
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
