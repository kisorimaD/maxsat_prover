#include "cnf.h"
#include <iostream>
#include <set>

using namespace std;

Literal::Literal(){
    id = 0;
};

Literal::Literal(string var, bool is_inv){
    if (VAR2ID.count(var) != 0)
    { 
        id = VAR2ID[var];
        inv = is_inv;
    }
    else
    {
        id = ID_COUNTER;
        ID_COUNTER++;
        
        ID2VAR[id] = var;
        VAR2ID[var] = id;

        inv = is_inv;
    }
}

Literal::Literal(int _id, bool is_inv)
{
    id = _id;
    inv = is_inv;
}

Literal Literal::neg() const
{
    return Literal(id, !inv);
}


// Clause::Clause(vector <Literal&> &_lits)
// { 
    
// }


void print_clause(Clause &c)
{
    int n = c.lits.size();

    if (n == 0)
    {
        cout << "( )";
        return;
    }

    cout << "( ";
 
    int i = 0;
    for(auto &lit : c.lits)
    {
        if(lit->inv)
        {
            cout << "¬";
        }
        cout << ID2VAR[lit->id];

        if(i != n - 1)
            cout << " ∧ ";

        i++;
    }

    cout << " )";
}

void preprocess()
{ 
    ID2VAR[0] = "?";
    VAR2ID["?"] = 0;
}

// RRuleInfo RRule1(vector <Clause> &cnf)
// {
//     int cr = 0;
//     map<int, bool> seen_literals;

//     for (Clause &c : cnf)
//     {
//         seen_literals.clear();
//         bool reduce_found = false;

//         for(Literal *l : c.lits)
//         {
//             if(seen_literals.count(l->id) != 0)
//             {
//                 if (seen_literals[l->id] != l->inv)
//                 {
//                     reduce_found = true;
//                     break;
//                 }
//             }
//         }
//     }
// }

int main()
{
    preprocess();

    Literal a("a");
    Literal b("b");

    Literal na = a.neg();
    vector <Literal *> vec_lits = {&a, &b, &na, &UNKNOWN_LITERAL};
    Clause c(vec_lits);
    
    print_clause(c);

    Clause unk;

    print_clause(unk);

}
