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

// Takes the element by reference.
struct PositiveRef {
    bool operator()(const int& x) const { return x > 0; }
};

// Whether x is positive, computed as x + 1 > 1: undefined on INT_MAX.
struct IncPositive {
    bool operator()(int x) const { return x + 1 > 1; }
};

// Counts its calls through a pointer that all copies share.
struct CountingPositive {
    unsigned* calls;
    bool operator()(int x) const {
        ++*calls;
        return x > 0;
    }
};

// Records the elements it is called on, in order, in a buffer of 3.
struct Logger {
    int* log;
    unsigned* len;
    bool operator()(int x) const {
        log[*len] = x;
        ++*len;
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
    int b[] = {0, 1};
    assert(!std::none_of(b, b + 2, Positive{}));
}

// An empty range calls nothing, so the predicate may be undefined on its elements, or
// even be a null function pointer.
void
TestEmpty() {
    int a[] = {2147483647};
    assert(std::all_of(a, a, IncPositive{}));
    assert(!std::any_of(a, a, IncPositive{}));
    assert(std::none_of(a, a, IncPositive{}));
    assert(std::all_of(a, a, PositiveRef{}));
    bool (*f)(int) = nullptr;
    assert(std::all_of(a, a, f));
}

void
TestByReference() {
    int a[] = {2, 4};
    assert(std::all_of(a, a + 2, PositiveRef{}));
    int b[] = {0, 2};
    assert(std::any_of(b, b + 2, PositiveRef{}));
}

// The algorithms stop at the first element that decides the result, before INT_MAX.
void
TestShortCircuit() {
    int a[] = {5, 2147483647};
    assert(std::any_of(a, a + 2, IncPositive{}));
    assert(!std::none_of(a, a + 2, IncPositive{}));
    int b[] = {0, 2147483647};
    assert(!std::all_of(b, b + 2, IncPositive{}));
}

void
TestFunctionPointer() {
    int a[] = {0, 0};
    assert(std::all_of(a, a + 2, &is_zero));
}

void
TestCounting() {
    int a[] = {1, 0, 2};
    unsigned calls = 0;
    assert(!std::all_of(a, a + 3, CountingPositive{&calls}));
    assert(calls == 2);
}

void
TestLogger() {
    int a[] = {3, 0, 4};
    int log[] = {0, 0, 0};
    unsigned len = 0;
    assert(!std::all_of(a, a + 3, Logger{log, &len}));
    assert(len == 2);
    assert(log[0] == 3);
}

void
TestLambda() {
    int a[] = {1, 2};
    auto big = [](int x) { return x > 5; };
    assert(std::none_of(a, a + 2, big));
    assert(!std::any_of(a, a + 2, big));
}

// Undefined behavior, which the specifications must reject. Not called.

// The predicate overflows on the second element.
bool
Overflow() {
    int a[] = {5, 2147483647};
    return std::all_of(a, a + 2, IncPositive{});
}

// Calls a null function pointer.
bool
NullFunctionPointer() {
    int a[] = {1};
    bool (*f)(int) = nullptr;
    return std::all_of(a, a + 1, f);
}

// [a + 2, a) is not a valid range.
bool
InvalidRange() {
    int a[] = {1, 2};
    return std::all_of(a + 2, a, Positive{});
}

int
main() {
    TestAllOf();
    TestAnyOf();
    TestNoneOf();
    TestEmpty();
    TestByReference();
    TestShortCircuit();
    TestFunctionPointer();
    TestCounting();
    TestLogger();
    TestLambda();
    return 0;
}
