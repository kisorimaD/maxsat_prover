#include <iostream>
#include "cnf.h"
#include <string>
#include <sstream>

int epoch_cnt = 0;
double C = -1;

double max_better = -1;
vector<int> max_better_branch;
CNF *best_cnf;

int progress_counter_test = 0;
void printProgress(double percentage)
{
    int pb_length = 60;
    int val = static_cast<int>(percentage * 100);
    int lpad = static_cast<int>(percentage * pb_length);
    int rpad = pb_length - lpad;
    std::cout << "\r" << val << "% [" << std::string(lpad, '#') << std::string(rpad, '-') << "]" << std::flush;
}

void branch_epoch(vector<CNF *> &variants, vector<int> &ids)
{
    cout << "Эпоха " << epoch_cnt++ << endl;

    cout << "Начинается примитивная фильтрация\n";
    vector<CNF *> filtered_variants;

    for (CNF *cnf : variants)
    {
        vector<int> naive_branch = cnf->branch(ids);
        double bf = branching_factor(naive_branch);

        if (bf < C)
        {
            if (bf > max_better)
            {
                max_better = bf;
                max_better_branch = naive_branch;
                best_cnf = cnf;
            }
        }
        else
        {
            filtered_variants.push_back(cnf);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    cout << "Осталось [" << filtered_variants.size() << "]. Начинается фильтрация с группировкой\n";

    bool need_pb = false;
    if (filtered_variants.size() > 300)
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

        if (bf < C)
        {
            if (bf > max_better)
            {
                max_better = bf;
                max_better_branch = group_branch;
                best_cnf = cnf;
            }
        }
        else
        {
            filtered_variants.push_back(cnf);
        }

        if (need_pb)
            progress_counter_test++;

        if (need_pb && progress_counter_test % 50 == 0)
        {
            printProgress((double)progress_counter_test / vsize);
        }
    }

    cout << "Было отфильтровано [" << variants.size() - filtered_variants.size() << "] вариантов. Это [" << (double)(variants.size() - filtered_variants.size()) / variants.size() * 100 << "%]\n";

    cout << "Осталось [" << filtered_variants.size() << "]\n\n";

    swap(variants, filtered_variants);
}

void solve()
{
    cout << "Введите через пробел branching vector, который задает branching factor, который требуется побить\n";

    std::string l;
    getline(cin, l);
    stringstream ss(l);
    string token;

    vector<int> C_branch;

    while (getline(ss, token, ' '))
    {
        C_branch.push_back(stoi(token));
    }
    cout << endl;

    C = branching_factor(C_branch);

    cout << "Оценка: " << C << "\n\n";

    vector<string> names = {"x", "y", "z"};
    int max_epoch = names.size();

    cout << "Начинается перебор вариантов\n";

    CNF init;

    vector<CNF *> variants = {&init};
    vector<int> ids;

    while (epoch_cnt < max_epoch)
    {
        cout << "Добавляется (4, 1)-singleton литерал " << names[epoch_cnt] << endl;

        Literal new_lit(names[epoch_cnt]);
        ids.push_back(new_lit.id);

        vector<CNF *> new_lit_variants;

        for (CNF *cnf : variants)
        {
            auto new_vars = add_new_var(cnf, names[epoch_cnt], 4, 1, SINGLETON);
            new_lit_variants.resize(new_lit_variants.size() + new_vars.size());
            copy(new_vars.begin(), new_vars.end(), new_lit_variants.rbegin());
        }

        swap(variants, new_lit_variants);

        cout << "Выполнено. Сейчас в рассмотрении " << variants.size() << " вариантов" << endl;
        cout << "Начинается бренчинг с фильтрацией \n\n";

        branch_epoch(variants, ids);

        if (variants.empty())
        {
            cout << "[ УСПЕХ ] Оценка ниже доказана!" << endl;
            cout << "Самый плохой случай ниже C: ";
            print_cnf(*best_cnf);

            cout << "Branch: ";
            for (int f : max_better_branch)
            {
                cout << f << " ";
            }
            cout << endl;

            cout << "Branch factor: " << max_better << endl;

            return;
        }
    }

    cout << "Осталось " << variants.size() << " вариантов.\n";

    int head_count = 30;

    cout << "Вывожу первые " << min((int)variants.size(), head_count) << '\n';

    int count3 = 0;
    for(CNF *cnf : variants)
    {  
        bool has3 = false;
        for(Clause *c : cnf->clauses)
        {
            if (c->lits.size() >= 4)
            {
                has3 = true;
                break;
            }
        }

        if(has3)
            count3++;
    }

    cout << "Клозу с хотя бы 3 переменными имеет [" << count3 << "]\n";
    cout << "Без клозы с 3 переменными [" << variants.size() - count3 << "]\n";  

    for (int i = 0; i < min((int)variants.size(), head_count); ++i)
    {
        print_cnf(*variants[i]);
        cout << '\n';
    }
}