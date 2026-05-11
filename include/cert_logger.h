#ifndef CERT_LOGGER_H
#define CERT_LOGGER_H

#include <iostream>
#include <fstream>
#include <vector>
#include <string>

class CNF; // Предварительное объявление графа формулы

class TreeLogger {
private:
    std::ofstream out;
    int indent_level;
    bool needs_comma;

    void print_indent();
    void write_formula(CNF* cnf);

public:
    TreeLogger(const std::string& filename, double target_bound);
    ~TreeLogger();

    // Класс-обертка для управления жизненным циклом узла JSON
    class NodeScope {
        TreeLogger& logger;
    public:
        NodeScope(TreeLogger& l) : logger(l) {}
        ~NodeScope() { logger.close_node(); }
    };

    NodeScope open_node();
    void close_node();
    
    void begin_children();
    void end_children();

    // Методы регистрации грануляции
    void log_add_var(const std::string& id, const std::string& var, CNF* cnf);
    void log_divide(const std::string& id, int clause_idx, CNF* cnf);
    void log_reduction(const std::string& id, const std::string& rule, int pivot, CNF* cnf);
    void log_branch(const std::string& id, int pivot, CNF* cnf);
    void log_leaf(const std::string& id, const std::vector<int>& vec, double tau, CNF* cnf, const std::vector<int>& partition);
};

extern TreeLogger global_logger;

#endif