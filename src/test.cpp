#include "cnf.h"
#include "test.h"
#include "cert_logger.h"

#include <algorithm>
#include <assert.h>
#include <iostream>
#include <sstream>
#include <iomanip>
#include <functional>

using namespace std;


// Вспомогательная функция для сборки временного CNF из слепка
CNF* create_dummy_cnf(const std::vector<std::vector<int>>& snap) {
    CNF* cnf = new CNF();
    for(const auto& cl : snap) {
        std::vector<Literal*> lits;
        for(int v : cl) {
            if(v == 0) lits.push_back(&UNKNOWN_LITERAL);
            else if(v == 1) lits.push_back(&UNKNOWN_NOT_EMPTY_LITERAL);
            else lits.push_back(new Literal(abs(v), v < 0)); 
        }
        cnf->clauses.push_back(new Clause(lits));
    }
    return cnf;
}

// Очистка фиктивного CNF
void delete_dummy_cnf(CNF* cnf) {
    for(Clause* c : cnf->clauses) {
        for(Literal* l : c->lits) {
            if(l != &UNKNOWN_LITERAL && l != &UNKNOWN_NOT_EMPTY_LITERAL) delete l;
        }
        delete c;
    }
    delete cnf;
}

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
{}

static vector<vector<int>> sorted_snapshot(CNF *cnf)
{
    vector<vector<int>> snapshot = cnf->get_snapshot();
    for (auto &clause : snapshot)
        sort(clause.begin(), clause.end());
    sort(snapshot.begin(), snapshot.end());
    return snapshot;
}

static void check_constructive_reduction(const vector<vector<int>> &input,
                                         const string &expected_rule,
                                         int expected_decrease,
                                         vector<vector<int>> expected_formula,
                                         bool isolate_rule = false)
{
    CNF *cnf = create_dummy_cnf(input);
    ReductionStep step = isolate_rule
                             ? apply_named_reduction(*cnf, expected_rule)
                             : apply_first_reduction(*cnf);
    assert(step.applied);
    assert(step.rule == expected_rule);
    assert(step.decrease == expected_decrease);
    for (auto &clause : expected_formula)
        sort(clause.begin(), clause.end());
    sort(expected_formula.begin(), expected_formula.end());
    assert(sorted_snapshot(step.cnf) == expected_formula);
    destroy_cnf(step.cnf);
    delete_dummy_cnf(cnf);
}

void test_constructive_reductions()
{
    check_constructive_reduction({{2, -2, 3}, {4, 0}},
                                 "RR1", 1, {{4, 0}}, true);
    check_constructive_reduction({{2, 0}, {-2, 1}},
                                 "RR2", 1, {{0, 1}});
    check_constructive_reduction({{2}, {2, 0}, {-2, 1}},
                                 "RR3", 2, {{1}});
    check_constructive_reduction({{2, 3}, {-2, 3}, {2, 0}, {-2, 1},
                                  {-3, 0}, {-3, 1}},
                                 "RR4", 1,
                                 {{3}, {2, 0}, {-2, 1}, {-3, 0}, {-3, 1}});
    check_constructive_reduction({{2, 3}, {2, 4}, {-2, 5}},
                                 "RR5", 1,
                                 {{3, 5}, {-3, 4, 5}}, true);
    check_constructive_reduction({{2, 0}, {2, 1}, {-2, 3, 0},
                                  {3, 1}, {-3, 0}},
                                 "RR6", 1,
                                 {{3, 0}, {3, 0, 1}, {3, 1}, {-3, 0}});
    check_constructive_reduction({{2, 3}, {2, 3, 4},
                                  {-2, -3, 5}, {-3, 6}},
                                 "RR7", 0,
                                 {{2, -2}, {2, -2, 4},
                                  {-2, 2, 5}, {2, 6}}, true);
    check_constructive_reduction({{2, 3, 4}, {-2, -3, 5}, {-2, 6}},
                                 "RR8", 1,
                                 {{-2, -3, 5}, {-2, 6}}, true);
    check_constructive_reduction({{2, 4}, {2, 5},
                                  {-2, 3, 6}, {-2, 3, 7}, {-3}},
                                 "RR9", 0,
                                 {{3, 4, 6}, {3, 4, 7},
                                  {3, 5, 6}, {3, 5, 7}, {-3}}, true);

    CNF *cascade_input = create_dummy_cnf({{2, 3}, {-2, 3}, {-3, 0}});
    ReductionFixpoint cascade = reduce_to_fixpoint(*cascade_input);
    assert(cascade.total_decrease == 2);
    assert(cascade.steps.size() == 2);
    assert(cascade.steps[0].rule == "RR2");
    assert(cascade.steps[1].rule == "RR2");
    vector<vector<int>> cascade_expected = {{0}};
    assert(sorted_snapshot(cascade.cnf) == cascade_expected);
    destroy_cnf(cascade.cnf);
    delete_dummy_cnf(cascade_input);

    CNF *lemma3_input = create_dummy_cnf({{0, 4}, {0, -4}, {0, -4}});
    DirectLemmaResult lemma3 = find_best_direct_lemma23(*lemma3_input);
    assert(lemma3.applied);
    assert(lemma3.rule == "lemma3");
    assert(lemma3.vec == vector<int>({1, 8}));
    delete_dummy_cnf(lemma3_input);

    // Regression from the remaining (3,2)-case: after either assignment of
    // x, z becomes a 3-variable and Lemma 3 must be composed in the child.
    CNF *child_pipeline = create_dummy_cnf({
        {0, 2, 3}, {0, 2, 4}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3}, {0, 3}, {-3}, {0, -4}, {0, -4}});
    ProofNode child_result = child_pipeline->xiao_branch(1);
    vector<int> expected_child_vec = {11, 10, 4, 3};
    sort(expected_child_vec.begin(), expected_child_vec.end(), greater<int>());
    assert(child_result.vec == expected_child_vec);
    assert(child_result.tau < 1.28855);
    ProofNode grouped_child = child_pipeline->branch_group({2, 3, 4});
    assert(grouped_child.vec == expected_child_vec);
    assert(grouped_child.tau < 1.28855);
    delete_dummy_cnf(child_pipeline);

    // Step 5.3: z is a (4,1)-singleton.  Continue with RR6 in z=1,
    // but leave z=0 as a recursive stop instead of forcing Lemma 2 there.
    CNF *step53_input = create_dummy_cnf({
        {0, 2, 3}, {0, 2}, {0, 2}, {1, -2, 3}, {0, -2, 4},
        {0, 3, 4}, {0, 3, 4}, {-3}, {0, 4}, {-4}});
    vector<int> expected_step53 = {6, 1};
    ProofNode step53_xiao = step53_input->xiao_branch(1);
    assert(step53_xiao.vec == expected_step53);
    assert(step53_xiao.tau < 1.28855);
    ProofNode step53_group = step53_input->branch_group({2, 3, 4});
    assert(step53_group.tau <= step53_xiao.tau + 1e-12);
    delete_dummy_cnf(step53_input);

    auto check_step55 = [&](const vector<vector<int>> &formula)
    {
        CNF *input = create_dummy_cnf(formula);
        vector<int> expected = {11, 10, 4, 3};
        ProofNode xiao = input->xiao_branch(1);
        assert(xiao.vec == expected);
        assert(xiao.tau < 1.28855);
        ProofNode grouped = input->branch_group({2, 3, 4});
        assert(grouped.tau <= xiao.tau + 1e-12);
        delete_dummy_cnf(input);
    };

    check_step55({
        {1, 2}, {0, 2}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3, 4}, {0, 3}, {-3}, {0, 4}, {-4}});
    check_step55({
        {1, 2}, {0, 2}, {0, 2}, {0, -2, 3}, {0, -2, 4},
        {0, 3}, {0, 3}, {-3}, {0, 4}, {0, 4}, {-4}});

    cout << "RR1--RR9 constructive tests passed\n";
}

void test_branching_factor()
{
    cout << branching_factor({6, 6, 5, 5}) << endl;
    cout << branching_factor({1, 2}) << endl;
    cout << branching_factor({4}) << endl;
}

void test_branch_three_vars()
{}

void test_branch_two_vars()
{}

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

    // CNF cnf;

    // CNF *with_x = add_new_var(&cnf, "x", 2, 3, ANY).at(0);

    // cout << "Добавляем в рассмотрение первую переменную х (3, 2)";

    // print_cnf(*with_x);

    // cout << "Добавляем переменную y (3, 2)-литерал\n";

    // vector<CNF *> with_y = add_new_var(with_x, "y", 4, 1, SINGLETON);

    // cout << "Размер: " << with_y.size() << endl;

    // cout << "Введите номер клозы для проверки разбора. -1 для окончания теста\n";

    // int k;
    // cin >> k;

    // vector<string> vars = {"x", "y"};

    // Literal x = Literal("x");
    // Literal y = Literal("y");

    // while (k != -1)
    // {
    //     pretty_branch_print(vars, with_y.at(k));

    //     vector<int> reg_branch = with_y.at(k)->branch({x.id, y.id});
    //     vector<int> group_branch = with_y.at(k)->branch_group({x.id, y.id});

    //     cout << "Regular Branch:\n";
    //     for (int r : reg_branch)
    //         cout << r << " ";
    //     cout << endl;

    //     cout << "Group Branch:\n";
    //     for (int r : group_branch)
    //         cout << r << " ";
    //     cout << endl;

    //     cin >> k;
    // }
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

int progress_counter_test = 0;

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

    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        ProofNode naive_node = cnf->branch(ids); // Используем ProofNode

        if (naive_node.tau >= C)
        {  
            filtered_variants.push_back(cnf);
        }
        else
        {
            global_logger.log_proof_tree(cnf->node_id, naive_node);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    if(is_xiao_branch)
    {
        cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с Reduction Rules\n";

        swap(filtered_variants, variants);
        filtered_variants.clear();

        for (int i = 0; i < variants.size(); ++i)
        {
            CNF *cnf = variants[i];
            ProofNode rr_node = cnf->xiao_branch(xiao_depth);

            if (rr_node.tau >= C) {
                filtered_variants.push_back(cnf);
            }
            else
            {
                global_logger.log_proof_tree(cnf->node_id, rr_node);
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


    for (int i = 0; i < variants.size(); ++i)
    {
        CNF *cnf = variants[i];
        bool flag = false;
        
        for (int k = 2; k <= ids.size(); ++k) {
            ProofNode approx_node = cnf->branch_group(ids, k);
            if (approx_node.tau < C) {
                global_logger.log_proof_tree(cnf->node_id, approx_node);
        
                flag = true;
                break;
            }
        }

        if (!flag) {
            ProofNode full_group_node = cnf->branch_group(ids, -1);
            if (full_group_node.tau >= C) {
                filtered_variants.push_back(cnf);
            }
            else
            {
                global_logger.log_proof_tree(cnf->node_id, full_group_node);
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

    double C = 1.28855;
    // C = 1.2873;

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
            {1, 4, SINGLETON},
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

            if (i < 0 || i >= (int)cur.size())
            {
                cout << "Формулы с индексом " << i
                     << " сейчас нет; осталось [" << cur.size()
                     << "] вариантов.\n\n";
                continue;
            }

            pretty_branch_print(vars, cur.at(i));
            cout << endl;

            ProofNode reg_node = cur.at(i)->branch(ids);
            ProofNode group_node = cur.at(i)->branch_group(ids);
            ProofNode xiao_node = cur.at(i)->xiao_branch(1);

            vector<int> reg_branch = reg_node.vec;
            vector<int> group_branch = group_node.vec;
            vector<int> xiao_branch = xiao_node.vec;

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

                ProofNode reg_node = cur.at(i)->branch(ids);
                ProofNode group_node = cur.at(i)->branch_group(ids);
                ProofNode xiao_node = cur.at(i)->xiao_branch(1);

                vector<int> reg_branch = reg_node.vec;
                vector<int> group_branch = group_node.vec;
                vector<int> xiao_branch = xiao_node.vec;

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
                double gfactor = cur.at(i)->branch_group(ids).tau;
                
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
                double gfactor = cnf->branch_group(ids).tau;
                double xfactor = cnf->xiao_branch(1).tau;

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
                    DivideResult res = empty_divide(cnf);
                    if (res.cnf_empty != nullptr)
                    {
                        next_cur.push_back(res.cnf_empty);
                        next_cur.push_back(res.cnf_not_empty);
                        success_count++;
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
                cout << "Извините, пока что empty_divide работает только с -1\n\n";
                // if (i >= 0 && i < (int)cur.size())
                // {
                //     pair<CNF *, CNF *> res = empty_divide(cur[i]);
                //     if (res.first != nullptr)
                //     {
                //         // Удаляем старую формулу и на её место вставляем две новые
                //         CNF* old_cnf = cur[i];
                //         cur.erase(cur.begin() + i);
                //         cur.insert(cur.begin() + i, res.second);
                //         cur.insert(cur.begin() + i, res.first);
                //         // delete old_cnf; // Не забывайте про освобождение памяти

                //         cout << "empty_divide успешно применен к формуле " << i << ".\n";
                //         cout << "Теперь в рассмотрении [" << cur.size() << "] вариантов.\n\n";
                //     }
                //     else
                //     {
                //         cout << "В формуле " << i << " не найдено литералов '?' для разбиения.\n\n";
                //     }
                // }
                // else
                // {
                //     cout << "Неверный индекс формулы.\n\n";
                // }
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

            cout << setprecision(10) << branching_factor(C_branch) << endl;

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

// -----------------------------------------------------------------------
// Тест: проверяет корректность всех разбиений из groups3.txt
//
// Каждое разбиение — строка из 8 символов (цифр), где s[i] — номер
// группы (класс) для i-й подстановки {x=бит0, y=бит1, z=бит2}.
// Для каждой группы вызываем check_group_validity с k=3.
// -----------------------------------------------------------------------
void test_groups3_validity()
{
    const int k = 3;  // Три переменных ветвления
    const int total_masks = 1 << k; // 8 подстановок

    if (valid_3_partitions.empty())
    {
        cout << "[SKIP] valid_3_partitions не загружены (запустите preprocess())\n";
        return;
    }

    int total   = (int)valid_3_partitions.size();
    int ok_cnt  = 0;
    int bad_cnt = 0;

    cout << "Проверяем " << total << " разбиений из groups3.txt...\n";

    for (int pi = 0; pi < total; ++pi)
    {
        const string& part = valid_3_partitions[pi];

        if ((int)part.size() != total_masks)
        {
            cout << "[BAD #" << pi << "] Строка \"" << part
                 << "\" имеет неверную длину " << part.size()
                 << " (ожидается " << total_masks << ")\n";
            bad_cnt++;
            continue;
        }

        // Определяем, сколько классов и какие маски в каждом
        int max_class = 0;
        for (char ch : part)
            max_class = max(max_class, (int)(ch - '0'));

        bool partition_ok = true;

        for (int cls = 0; cls <= max_class; ++cls)
        {
            // Собираем маски этого класса
            vector<int> group_masks;
            for (int mask = 0; mask < total_masks; ++mask)
                if ((int)(part[mask] - '0') == cls)
                    group_masks.push_back(mask);

            if (group_masks.empty())
                continue; // пропуск несуществующего класса

            string diag;
            bool group_ok = check_group_validity(group_masks, k, diag);

            if (!group_ok)
            {
                if (partition_ok)
                {
                    // Первая ошибка в этом разбиении — выводим заголовок
                    cout << "\n[BAD #" << pi << "] Разбиение: \"" << part << "\"\n";
                }
                partition_ok = false;

                // Маски в группе с расшифровкой (xyz — бит0=x, бит1=y, бит2=z)
                cout << "  Класс " << cls << " (маски:";
                for (int m : group_masks)
                {
                    cout << " " << ((m >> 2) & 1) << ((m >> 1) & 1) << (m & 1);
                }
                cout << ")\n";
                cout << "  Причина: " << diag << "\n";
            }
        }

        if (partition_ok)
            ok_cnt++;
        else
            bad_cnt++;
    }

    cout << "\n=== Итог: " << ok_cnt << "/" << total << " разбиений корректны";
    if (bad_cnt == 0)
        cout << " — всё OK ✓\n";
    else
        cout << ", " << bad_cnt << " НЕКОРРЕКТНЫХ ✗\n";
}
