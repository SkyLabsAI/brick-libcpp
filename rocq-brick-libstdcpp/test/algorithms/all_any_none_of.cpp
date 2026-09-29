/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>

struct Positive {
    bool operator()(int x) const { return x > 0; }
};

// Counts its calls through a pointer that all copies share.
struct CountingPositive {
    int* calls;
    bool operator()(int x) const {
        ++*calls;
        return x > 0;
    }
};

bool
is_zero(int x) {
    return x == 0;
}

void
TestAllOf() {
    int a[] = {1, 2};
    assert(std::all_of(a, a + 2, Positive{}));
    int b[] = {1, 0};
    assert(!std::all_of(b, b + 2, Positive{}));
}

void
TestAnyOf() {
    int a[] = {0, 3};
    assert(std::any_of(a, a + 2, Positive{}));
    int b[] = {0, -1};
    assert(!std::any_of(b, b + 2, Positive{}));
}

void
TestNoneOf() {
    int a[] = {0, -1};
    assert(std::none_of(a, a + 2, Positive{}));
}

void
TestFunctionPointer() {
    int a[] = {0, 0};
    assert(std::all_of(a, a + 2, &is_zero));
}

void
TestCounting() {
    int a[] = {1, 0, 2};
    int calls = 0;
    assert(!std::all_of(a, a + 3, CountingPositive{&calls}));
    assert(calls <= 3);
}

void
TestLambda() {
    int a[] = {1, 2};
    auto big = [](int x) { return x > 5; };
    assert(std::none_of(a, a + 2, big));
    assert(!std::any_of(a, a + 2, big));
}

int
main() {
    TestAllOf();
    TestAnyOf();
    TestNoneOf();
    TestFunctionPointer();
    TestCounting();
    TestLambda();
    return 0;
}
