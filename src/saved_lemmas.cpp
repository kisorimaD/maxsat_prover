#include "lemmas.h"
#include "cnf.h"
#include "xiao_property2.h"

#include <algorithm>
#include <cerrno>
#include <cmath>
#include <filesystem>
#include <sstream>
#include <stdexcept>
#include <tuple>
#include <unistd.h>
#include <sys/wait.h>

namespace {
using Degree = std::array<int, 3>;
struct PatternClause { int tail; std::set<int> literals; };
struct SavedLemma {
    SavedLemmaSource source;
    std::string target_key;
    double q;
    bool imports;
    int step6_context = 0;
    std::vector<std::vector<Degree>> families;
    std::vector<int> vector;
    std::vector<PatternClause> clauses;
    std::vector<std::array<int, 4>> role_degrees; // positive, negative, positive/negative units
};
std::vector<SavedLemma> library;
std::vector<SavedLemmaSource> sources;
std::vector<Degree> degree_scope;
std::string search_target = "12873e-4";
std::uint64_t revision = 0;
SavedLemmaStats counters;

std::string decimal_key(std::string value)
{
    if (!value.empty() && value[0] == '+') value.erase(0, 1);
    auto e = value.find_first_of("eE");
    int exponent = e == std::string::npos ? 0 : std::stoi(value.substr(e + 1));
    if (e != std::string::npos) value.resize(e);
    auto point = value.find('.');
    if (point != std::string::npos)
    {
        exponent -= static_cast<int>(value.size() - point - 1);
        value.erase(point, 1);
    }
    auto first = value.find_first_not_of('0');
    if (first == std::string::npos) throw std::invalid_argument("target must exceed one");
    value.erase(0, first);
    while (value.size() > 1 && value.back() == '0') { value.pop_back(); ++exponent; }
    return value + "e" + std::to_string(exponent);
}

std::string unhex(const std::string &value)
{
    if (value.size() % 2) throw std::runtime_error("invalid lemma index string");
    std::string result;
    auto digit = [](char c) {
        if (c >= '0' && c <= '9') return c - '0';
        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
        throw std::runtime_error("invalid lemma index hex digit");
    };
    for (std::size_t i = 0; i < value.size(); i += 2)
        result.push_back(static_cast<char>(16 * digit(value[i]) + digit(value[i + 1])));
    return result;
}

std::string compile_index(const std::vector<std::string> &files)
{
    // Use argv directly, never a shell. Python validates proofs once at startup.
    auto script = std::filesystem::canonical("/proc/self/exe").parent_path() / "compile_lemmas.py";
    std::vector<std::string> arguments = {"python3", script.string()};
    arguments.insert(arguments.end(), files.begin(), files.end());
    std::vector<char*> argv;
    for (auto &argument : arguments) argv.push_back(argument.data());
    argv.push_back(nullptr);
    int descriptors[2];
    if (pipe(descriptors) != 0) throw std::runtime_error("cannot create lemma loader pipe");
    pid_t child = fork();
    if (child < 0)
    {
        close(descriptors[0]); close(descriptors[1]);
        throw std::runtime_error("cannot start lemma loader");
    }
    if (child == 0)
    {
        close(descriptors[0]);
        if (descriptors[1] != STDOUT_FILENO)
        {
            if (dup2(descriptors[1], STDOUT_FILENO) < 0) _exit(127);
            close(descriptors[1]);
        }
        execvp(argv[0], argv.data());
        _exit(127);
    }
    close(descriptors[1]);
    std::string output;
    char buffer[8192];
    bool failed = false;
    for (;;)
    {
        ssize_t count = read(descriptors[0], buffer, sizeof(buffer));
        if (count == 0) break;
        if (count < 0) { if (errno == EINTR) continue; failed = true; break; }
        output.append(buffer, static_cast<std::size_t>(count));
    }
    close(descriptors[0]);
    int status;
    while (waitpid(child, &status, 0) < 0)
        if (errno != EINTR) throw std::runtime_error("cannot wait for lemma loader");
    if (failed || !WIFEXITED(status) || WEXITSTATUS(status) != 0)
        throw std::runtime_error("saved lemma validation failed (see loader error)");
    return output;
}

template<class T> T read_value(std::istream &stream)
{
    T result;
    if (!(stream >> result)) throw std::runtime_error("invalid saved lemma index");
    return result;
}

bool covered(const Degree &degree, const std::vector<Degree> &family)
{
    return std::any_of(family.begin(), family.end(), [&](const Degree &allowed) {
        return degree[0] == allowed[0] && degree[1] == allowed[1] &&
               (!allowed[2] || degree[2]);
    });
}

bool eligible(const SavedLemma &lemma, double q, int step6_context)
{
    if ((lemma.step6_context & step6_context) != lemma.step6_context) return false;
    // Resolution can duplicate hidden literals from D. The original degree
    // family is no longer a premise for those literals in the child formula.
    if (MaxSATSettings.LEMMA3_RESOLUTION_CONTEXT && !lemma.families.empty()) return false;
    if (lemma.q != q || lemma.target_key != search_target ||
        (lemma.imports && !MaxSATSettings.ALLOW_NAMED_ASSUMPTIONS)) return false;
    if (!lemma.families.empty() && degree_scope.empty()) return false;
    for (const auto &family : lemma.families)
        for (const auto &degree : degree_scope)
            if (!covered(degree, family)) return false;
    return true;
}

class Matcher {
    const SavedLemma &lemma;
    const CNF &formula;
    const std::map<int, FormulaVarStats> &stats;
    std::vector<std::set<int>> actual;
    std::vector<std::vector<int>> candidates;
    std::vector<int> roles, order, witnesses;

    std::set<int> projection(int clause) const
    {
        std::set<int> result;
        for (std::size_t role = 0; role < roles.size(); ++role)
            if (roles[role])
            {
                if (actual[clause].count(roles[role])) result.insert(static_cast<int>(role) + 1);
                if (actual[clause].count(-roles[role])) result.insert(-static_cast<int>(role) - 1);
            }
        return result;
    }

    bool partial_match() const
    {
        for (const auto &pattern : lemma.clauses)
        {
            std::set<int> expected;
            for (int lit : pattern.literals) if (roles[std::abs(lit) - 1]) expected.insert(lit);
            bool found = false;
            for (std::size_t index = 0; index < actual.size(); ++index)
            {
                if (pattern.tail == -1 && (!formula.clauses[index]->tail_atoms.empty() ||
                                          actual[index].size() != pattern.literals.size())) continue;
                if (actual[index].size() < pattern.literals.size()) continue;
                if (projection(static_cast<int>(index)) == expected) { found = true; break; }
            }
            if (!found) return false;
        }
        return true;
    }

    bool match_clauses()
    {
        std::set<int> available;
        for (std::size_t index = 0; index < actual.size(); ++index)
            if (!projection(static_cast<int>(index)).empty()) available.insert(static_cast<int>(index));
        if (available.size() != lemma.clauses.size()) return false;
        std::vector<int> clause_order;
        for (std::size_t i = 0; i < lemma.clauses.size(); ++i) clause_order.push_back(static_cast<int>(i));
        auto rank = [&](int i) { return lemma.clauses[i].tail == -1 ? 0 : lemma.clauses[i].tail == 1 ? 1 : 2; };
        std::stable_sort(clause_order.begin(), clause_order.end(), [&](int a, int b) { return rank(a) < rank(b); });
        witnesses.clear();
        for (int index : clause_order)
        {
            const auto &pattern = lemma.clauses[index];
            bool found = false;
            for (int parent : available)
            {
                auto displayed = projection(parent);
                if (displayed != pattern.literals) continue;
                bool remainder = !formula.clauses[parent]->tail_atoms.empty();
                bool nonempty = false, compatible = true;
                for (const auto &[tail, guaranteed] : formula.clauses[parent]->tail_atoms) nonempty |= guaranteed;
                for (int lit : actual[parent])
                {
                    if (std::any_of(roles.begin(), roles.end(), [&](int role) { return std::abs(role) == std::abs(lit); })) continue;
                    remainder = nonempty = true;
                    if (!lemma.families.empty())
                    {
                        const auto &s = stats.at(std::abs(lit));
                        int p = lit > 0 ? s.pos_count : s.neg_count;
                        int n = lit > 0 ? s.neg_count : s.pos_count;
                        int units = lit > 0 ? s.neg_unit_count : s.pos_unit_count;
                        if (!covered({p, n, n == 1 && units == 1}, degree_scope)) compatible = false;
                    }
                }
                if (!compatible || (pattern.tail == -1 && remainder) || (pattern.tail == 1 && !nonempty)) continue;
                if (pattern.tail == -1) witnesses.push_back(parent);
                available.erase(parent);
                found = true;
                break;
            }
            if (!found) return false;
        }
        return available.empty();
    }

    bool assign(std::size_t depth)
    {
        if (depth == order.size()) return match_clauses();
        int role = order[depth];
        for (int candidate : candidates[role])
        {
            if (std::any_of(roles.begin(), roles.end(), [&](int old) { return std::abs(old) == std::abs(candidate); })) continue;
            roles[role] = candidate;
            if (partial_match() && assign(depth + 1)) return true;
            roles[role] = 0;
        }
        return false;
    }

public:
    Matcher(const SavedLemma &definition, const CNF &input, const std::map<int, FormulaVarStats> &statistics)
        : lemma(definition), formula(input), stats(statistics), roles(definition.role_degrees.size(), 0)
    {
        for (std::size_t role = 0; role < roles.size(); ++role)
        {
            auto required = lemma.role_degrees[role];
            candidates.emplace_back();
            for (const auto &[id, s] : stats)
            {
                if (s.pos_count == required[0] && s.neg_count == required[1] &&
                    s.pos_unit_count >= required[2] && s.neg_unit_count >= required[3]) candidates.back().push_back(id);
                if (s.neg_count == required[0] && s.pos_count == required[1] &&
                    s.neg_unit_count >= required[2] && s.pos_unit_count >= required[3]) candidates.back().push_back(-id);
            }
            if (candidates.back().empty()) return;
            order.push_back(static_cast<int>(role));
        }
        for (Clause *clause : formula.clauses)
        {
            std::set<int> literals;
            for (Literal *lit : clause->lits)
                if (!is_any_unknown_literal(lit)) literals.insert(lit->inv ? -lit->id : lit->id);
            actual.push_back(std::move(literals));
        }
        std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return candidates[a].size() < candidates[b].size(); });
    }

    bool match(LemmaApplication &result)
    {
        if (std::any_of(candidates.begin(), candidates.end(), [](const auto &list) { return list.empty(); })) return false;
        if (!assign(0)) return false;
        result = {lemma.source.id, roles, witnesses, lemma.vector, lemma.source.digest,
                  lemma.families.empty() ? std::vector<Degree>{} : degree_scope};
        return true;
    }
};
} // namespace

void load_saved_lemmas(const std::vector<std::string> &files)
{
    std::vector<SavedLemma> loaded;
    std::vector<SavedLemmaSource> loaded_sources;
    if (!files.empty())
    {
        std::istringstream input(compile_index(files));
        if (read_value<std::string>(input) != "maxsat-lemma-index-v2") throw std::runtime_error("unknown lemma index format");
        int count = read_value<int>(input);
        if (count != static_cast<int>(files.size())) throw std::runtime_error("lemma index count mismatch");
        for (int i = 0; i < count; ++i)
        {
            SavedLemma lemma;
            lemma.source.id = unhex(read_value<std::string>(input));
            lemma.source.digest = read_value<std::string>(input);
            lemma.source.path = unhex(read_value<std::string>(input));
            lemma.target_key = unhex(read_value<std::string>(input));
            lemma.q = read_value<double>(input);
            lemma.imports = read_value<int>(input) != 0;
            lemma.step6_context = read_value<int>(input);
            if (lemma.step6_context < 0 || lemma.step6_context > 3) throw std::runtime_error("invalid saved lemma context");
            int families = read_value<int>(input);
            for (int f = 0; f < families; ++f)
            {
                std::vector<Degree> family;
                int size = read_value<int>(input);
                for (int d = 0; d < size; ++d) family.push_back({read_value<int>(input), read_value<int>(input), read_value<int>(input)});
                lemma.families.push_back(std::move(family));
            }
            int roles = read_value<int>(input);
            if (roles < 1 || roles > MAX_MASK_BITS) throw std::runtime_error("invalid lemma role count");
            lemma.role_degrees.resize(roles, {0, 0, 0, 0});
            int size = read_value<int>(input);
            for (int v = 0; v < size; ++v) lemma.vector.push_back(read_value<int>(input));
            int clauses = read_value<int>(input);
            for (int c = 0; c < clauses; ++c)
            {
                PatternClause clause;
                clause.tail = read_value<int>(input);
                int literals = read_value<int>(input);
                for (int l = 0; l < literals; ++l)
                {
                    int literal = read_value<int>(input);
                    if (literal == 0 || std::abs(literal) > roles) throw std::runtime_error("invalid lemma role literal");
                    clause.literals.insert(literal);
                    auto &degree = lemma.role_degrees[std::abs(literal) - 1];
                    ++degree[literal > 0 ? 0 : 1];
                    if (literals == 1 && clause.tail == -1) ++degree[literal > 0 ? 2 : 3];
                }
                lemma.clauses.push_back(std::move(clause));
            }
            loaded_sources.push_back(lemma.source);
            loaded.push_back(std::move(lemma));
        }
        if (input >> std::ws && !input.eof()) throw std::runtime_error("extra data in lemma index");
    }
    library = std::move(loaded);
    sources = std::move(loaded_sources);
    counters = {library.size(), 0, 0};
    ++revision;
}

const std::vector<SavedLemmaSource> &saved_lemma_sources() { return sources; }
SavedLemmaStats saved_lemma_stats() { return counters; }
std::uint64_t saved_lemma_policy_revision() { return revision; }

void set_lemma_search_target(const std::string &decimal)
{
    std::size_t consumed;
    double q = std::stod(decimal, &consumed);
    if (consumed != decimal.size() || decimal.find_first_not_of("0123456789.+-eE") != std::string::npos || !std::isfinite(q) || q <= 1)
        throw std::invalid_argument("target must be a finite decimal greater than one");
    auto key = decimal_key(decimal);
    if (lemma_export_enabled() && key != decimal_key(lemma_export_settings.target))
        throw std::invalid_argument("a lemma-export session has a fixed target q");
    if (key != search_target) { search_target = std::move(key); ++revision; }
}

void set_lemma_degree_scope(const std::vector<LiteralDegType> &degrees)
{
    std::set<Degree> normalized;
    for (const auto &degree : degrees)
    {
        validate_degree(degree.i, degree.j, degree.type);
        normalized.insert({degree.i, degree.j, degree.type == SINGLETON});
    }
    std::vector<Degree> updated(normalized.begin(), normalized.end());
    if (updated != degree_scope) { degree_scope = std::move(updated); ++revision; }
}

bool lemma_degree_scope_is_step6()
{
    return !degree_scope.empty() && std::all_of(degree_scope.begin(), degree_scope.end(),
        [](const Degree &d) {
            return (d[0] == 2 && d[1] == 2) ||
                   ((d[0] == 3 || d[0] == 4) && d[1] == 1 && d[2]);
        });
}

std::vector<std::array<int, 3>> lemma_current_degree_scope() { return degree_scope; }

std::vector<LemmaApplication> find_saved_lemma_applications(const CNF &formula, double q, int step6_context)
{
    if (step6_context < 0)
        step6_context = int(MaxSATSettings.ALLOW_XIAO_PROPERTY1) | (2 * int(MaxSATSettings.ALLOW_XIAO_PROPERTY2));
    if (library.empty()) return {};
    if (std::none_of(library.begin(), library.end(), [&](const SavedLemma &lemma) { return eligible(lemma, q, step6_context); })) return {};
    auto stats = analyze_formula(formula);
    std::vector<LemmaApplication> result;
    for (const auto &lemma : library)
    {
        if (!eligible(lemma, q, step6_context)) continue;
        if (lemma.step6_context && !xiao_step6_context_eligible(formula)) continue;
        ++counters.attempts;
        LemmaApplication application;
        if (Matcher(lemma, formula, stats).match(application))
        {
            ++counters.matches;
            result.push_back(std::move(application));
        }
    }
    return result;
}
