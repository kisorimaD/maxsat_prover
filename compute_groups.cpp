#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <set>
#include <unordered_set>
#include <fstream>
#include <sstream>

using namespace std;


unordered_set<string> valid_matrices;



bool is_valid_mask[256];




int bits[8][3];

void init_bits() {
    for (int i = 0; i < 8; ++i) {
        bits[i][0] = (i >> 2) & 1;
        bits[i][1] = (i >> 1) & 1;
        bits[i][2] = (i >> 0) & 1;
    }
}




string get_canonical(const vector<int>& row_values) {
    if (row_values.empty()) return "";
    
    size_t m = row_values.size(); 
    string min_s = "~"; 

    
    vector<int> p = {0, 1, 2};
    do {
        
        vector<string> current_rows(m);
        
        for (size_t i = 0; i < m; ++i) {
            int val = row_values[i];
            
            string r = "000";
            r[0] = bits[val][p[0]] + '0';
            r[1] = bits[val][p[1]] + '0';
            r[2] = bits[val][p[2]] + '0';
            current_rows[i] = r;
        }

        
        
        sort(current_rows.begin(), current_rows.end());

        
        string s = "";
        s.reserve(3 * m);
        for (const string& row_str : current_rows) {
            s += row_str;
        }

        
        if (s < min_s) {
            min_s = s;
        }

    } while (next_permutation(p.begin(), p.end()));

    return min_s;
}


int assignment[8]; 
vector<string> results_output;


void solve(int idx, int num_groups) {
    if (idx == 8) {
        
        bool ok = true;
        for (int g = 1; g <= num_groups; ++g) {
            int mask = 0;
            for (int i = 0; i < 8; ++i) {
                if (assignment[i] == g) {
                    mask |= (1 << i);
                }
            }
            
            if (!is_valid_mask[mask]) {
                ok = false;
                break;
            }
        }

        if (ok) {
            string res = "";
            for (int i = 0; i < 8; ++i) {
                res += to_string(assignment[i]) + (i == 7 ? "" : "");
            }
            results_output.push_back(res);
        }
        return;
    }

    
    for (int g = 1; g <= num_groups; ++g) {
        assignment[idx] = g;
        solve(idx + 1, num_groups);
    }

    
    assignment[idx] = num_groups + 1;
    solve(idx + 1, num_groups + 1);
}

int main() {
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);

    init_bits();

    ifstream infile("matrices.txt");
    if (!infile.is_open()) {
        return 1; 
    }

    int N;
    
    if (infile.is_open()) {
        infile >> N;
        string line;
        getline(infile, line); 
        for(int i=0; i<N; ++i) {
            infile >> line;
            if(!line.empty()) valid_matrices.insert(line);
        }
        infile.close();
    } else {
        return 1;
    }

    
    
    for (int mask = 1; mask < 256; ++mask) {
        vector<int> rows;
        for (int i = 0; i < 8; ++i) {
            if ((mask >> i) & 1) {
                rows.push_back(i);
            }
        }
        
        string canon = get_canonical(rows);
        
        if (valid_matrices.count(canon)) {
            is_valid_mask[mask] = true;
        } else {
            is_valid_mask[mask] = false;
        }
    }

    
    
    assignment[0] = 1;
    solve(1, 1);

    
    ofstream outfile("output.txt");
    outfile << results_output.size() << "\n";
    for (const string& s : results_output) {
        outfile << s << "\n";
    }
    outfile.close();

    return 0;
}
