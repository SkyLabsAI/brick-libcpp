/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <string>
#include <type_traits>

#include "alias.cpp"
#define main vector_test_main
#include "test.cpp"
#undef main

// Native-only: reserve/capacity and string operations have no client contracts
// here. From this repository:
//   dune build @rocq-brick-libstdcpp/test/vector/runtest
// From the workspace:
//   dune build @fmdeps/brick-libcpp/rocq-brick-libstdcpp/test/vector/runtest
template<class T>
void
CheckAppendAlias(const T& value, bool reallocate) {
    std::vector<T> v(1, value);
    if (reallocate) {
        while (v.size() < v.capacity()) {
            v.push_back(value);
        }
    } else {
        v.reserve(v.size() + 1);
    }
    const auto old_size = v.size();
    const auto old_capacity = v.capacity();
    const auto* old_data = v.data();
    assert((old_size + 1 > old_capacity) == reallocate);

    if constexpr (std::is_same_v<T, int>) {
        AliasAppend(v);
    } else {
        v.push_back(v[0]);
    }
    assert(v.size() == old_size + 1);
    assert(reallocate ? v.capacity() > old_capacity : v.capacity() == old_capacity);
    if (!reallocate) {
        assert(v.data() == old_data);
    }
    for (const auto& element : v) {
        assert(element == value);
    }
}

template<class T>
void
CheckFillAlias(const T& first, const T& fill, bool reallocate) {
    std::vector<T> v{first, fill};
    const auto new_size = reallocate ? v.capacity() + 2 : v.size() + 2;
    if (!reallocate) {
        v.reserve(new_size);
    }
    const auto old_capacity = v.capacity();
    const auto* old_data = v.data();
    assert((new_size > old_capacity) == reallocate);

    if constexpr (std::is_same_v<T, int>) {
        AliasFill(v, new_size);
    } else {
        v.resize(new_size, v[1]);
    }
    assert(v.size() == new_size);
    assert(reallocate ? v.capacity() > old_capacity : v.capacity() == old_capacity);
    if (!reallocate) {
        assert(v.data() == old_data);
    }
    assert(v[0] == first);
    for (std::size_t i = 1; i < v.size(); ++i) {
        assert(v[i] == fill);
    }
}

int
main() {
    assert(vector_test_main() == 0);
    const std::string a(128, 'a');
    const std::string b(128, 'b');
    for (bool reallocate : {false, true}) {
        CheckAppendAlias(7, reallocate);
        CheckFillAlias(9, 4, reallocate);
        CheckAppendAlias(a, reallocate);
        CheckFillAlias(a, b, reallocate);
    }
    return 0;
}
