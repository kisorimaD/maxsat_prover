#pragma once
#include "cnf.h"
#include <array>

// The imported theorem assumes a globally Xiao-reduced Step 6 instance.
// Local tests below are necessary conditions, not a check of hidden RRs.
std::array<bool, 2> xiao_property2_sides(const CNF &formula, int pivot);
std::array<bool, 2> xiao_property1_sides(const CNF &formula, int pivot);
bool xiao_step6_context_eligible(const CNF &formula);

struct DisableXiaoProperty2 {
    bool previous = MaxSATSettings.ALLOW_XIAO_PROPERTY2;
    bool previous1 = MaxSATSettings.ALLOW_XIAO_PROPERTY1;
    DisableXiaoProperty2() {
        MaxSATSettings.ALLOW_XIAO_PROPERTY2 = false;
        MaxSATSettings.ALLOW_XIAO_PROPERTY1 = false;
    }
    ~DisableXiaoProperty2() {
        MaxSATSettings.ALLOW_XIAO_PROPERTY2 = previous;
        MaxSATSettings.ALLOW_XIAO_PROPERTY1 = previous1;
    }
};
