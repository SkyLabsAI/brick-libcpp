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

void
TestPushBackAlias(vector<int>& v) {
    v.push_back(v[0]);
    test(v.size() == 2);
    test(v[0] == 7);
    test(v[1] == 7);
}

void
TestResizeAliasGrow(vector<int>& v) {
    v.resize(4, v[1]);
    test(v.size() == 4);
    test(v[0] == 9);
    test(v[1] == 4);
    test(v[2] == 4);
    test(v[3] == 4);
}

void
TestResizeAliasShrink(vector<int>& v) {
    v.resize(1, v[2]);
    test(v.size() == 1);
    test(v[0] == 1);
}

void
TestResizeAliasSame(vector<int>& v) {
    v.resize(3, v[2]);
    test(v.size() == 3);
    test(v[0] == 1);
    test(v[1] == 2);
    test(v[2] == 3);
}

void
TestResizeAliasEmpty(vector<int>& v) {
    v.resize(0, v[2]);
    test(v.size() == 0);
}

void
TestAliases() {
    vector<int> v;
    v.push_back(7);
    TestPushBackAlias(v);

    vector<int> w;
    w.push_back(9);
    w.push_back(4);
    TestResizeAliasGrow(w);

    vector<int> x;
    x.push_back(1);
    x.push_back(2);
    x.push_back(3);
    TestResizeAliasSame(x);
    TestResizeAliasShrink(x);

    vector<int> y;
    y.push_back(1);
    y.push_back(2);
    y.push_back(3);
    TestResizeAliasEmpty(y);
}

int
main() {
    TestBasic();
    TestAggregate();
    TestIntIter();
    TestForEach();
    TestAllocCtor();
    TestAliases();
    return 0;
}
