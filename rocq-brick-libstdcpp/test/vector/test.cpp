/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>
#include <memory>
#include <vector>

using namespace std;

void
test(bool b, const char* msg = nullptr) {
    assert(b);
}

void
TestBasic() {
    vector<int> v;
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    test(v[0] == 1);
    test(v[1] == 2);
    test(v[2] == 3);
    test(v.size() == 3);
}

void
TestIntIter() {
    vector<int> v;
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    auto it = std::find(v.begin(), v.end(), 2);
    test(*it == 2);
    it = v.begin();
    it++;
    auto it2 = std::find(it, v.end(), 1);
    auto it3 = v.end();
    test(it2 == it3);
}

unsigned
sum(const vector<unsigned>& v) {
    unsigned r = 0;
    for (auto x : v) {
        r += x;
    }
    return r;
}

void
TestForEach() {
    vector<unsigned> v{};
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    int r = sum(v);
    test(r == 6);
}

struct Aggregate {
    int x, y, z;
    Aggregate(const Aggregate &) = default;
    Aggregate(Aggregate &&) = default;
    Aggregate& operator=(const Aggregate &) = default;
    Aggregate& operator=(Aggregate &&) = default;

    Aggregate(int a) : x(a), y(a), z(a) {}
    bool operator==(Aggregate& other) {
        return x == other.x && y == other.y && z == other.z;
    }
    bool operator!=(Aggregate& other) {
        return !(*this == other);
    }
};

void
TestAggregate() {
    vector<Aggregate> v;
    Aggregate o1{1}, o2{2}, o3{3};
    test(o1 != o2);
    v.push_back(o1);
    v.push_back(o2);
    v.push_back(o3);
    test(v[0] == o1);
    test(v[1] == o2);
    test(v[2] == o3);
    test(v.size() == 3);
}

void
TestAllocCtor() {
    allocator<int> a;
    vector<int> v(a);
    test(v.size() == 0);
}

// Iterators are named before they are converted or compared, as in
// TestIntIter: binding a temporary iterator to a const reference needs
// wp_make_const on the locked iterator representation.
void
TestErase() {
    vector<int> v;
    v.push_back(1);
    v.push_back(2);
    v.push_back(3);
    vector<int>::iterator b = v.begin();
    vector<int>::const_iterator first = b;
    auto it = v.erase(first);
    test(*it == 2);
    test(v.size() == 2);
    vector<int>::iterator b1 = v.begin() + 1;
    vector<int>::const_iterator last = b1;
    auto it1 = v.erase(last);
    auto e1 = v.end();
    test(it1 == e1);
    vector<int>::iterator b2 = v.begin();
    vector<int>::iterator e2 = v.end();
    vector<int>::const_iterator f2 = b2;
    vector<int>::const_iterator l2 = e2;
    v.erase(f2, l2);
    test(v.size() == 0);
}

int
main() {
    TestBasic();
    TestAggregate();
    TestIntIter();
    TestForEach();
    TestAllocCtor();
    TestErase();
    return 0;
}
