/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <climits>
#include <cstddef>
#include <cstdint>
#include <limits>

void SizeTMax(std::size_t n) {
    assert(n <= std::numeric_limits<std::size_t>::max());
}

void IntMinBound(int n) {
    assert(std::numeric_limits<int>::min() <= n);
}

int main() {
    assert(std::numeric_limits<std::int64_t>::max() == INT64_MAX);
    assert(std::numeric_limits<int>::min() == INT_MIN);
    assert(std::numeric_limits<unsigned>::min() == 0);
    assert(std::numeric_limits<signed char>::min() == SCHAR_MIN);
    assert(std::numeric_limits<signed char>::max() == SCHAR_MAX);
    assert(std::numeric_limits<unsigned char>::min() == 0);
    assert(std::numeric_limits<unsigned char>::max() == UCHAR_MAX);
    assert(std::numeric_limits<short>::min() == SHRT_MIN);
    assert(std::numeric_limits<short>::max() == SHRT_MAX);
    assert(std::numeric_limits<unsigned short>::min() == 0);
    assert(std::numeric_limits<unsigned short>::max() == USHRT_MAX);
    assert(std::numeric_limits<long long>::min() == LLONG_MIN);
    assert(std::numeric_limits<long long>::max() == LLONG_MAX);
    assert(std::numeric_limits<unsigned long long>::min() == 0);
    assert(std::numeric_limits<unsigned long long>::max() == ULLONG_MAX);
    SizeTMax(0);
    SizeTMax(SIZE_MAX);
    IntMinBound(INT_MIN);
    IntMinBound(INT_MAX);
    return 0;
}
