/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>
#include <vector>

struct Positive {
    bool operator()(int x) const { return x > 0; }
};

void
TestVector() {
    std::vector<int> v;
    v.push_back(1);
    v.push_back(2);
    assert(*v.begin() == 1);
    assert(std::all_of(v.begin(), v.end(), Positive{}));
}

int
main() {
    TestVector();
    return 0;
}
