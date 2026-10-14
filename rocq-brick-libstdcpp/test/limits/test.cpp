/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <climits>
#include <cstddef>
#include <cstdint>
#include <limits>

bool SizeTMax(std::size_t n) {
    return n <= std::numeric_limits<std::size_t>::max();
}

bool Int64Max() {
    return std::numeric_limits<std::int64_t>::max() == INT64_MAX;
}

bool IntMin() {
    return std::numeric_limits<int>::min() == INT_MIN;
}

bool UnsignedMin() {
    return std::numeric_limits<unsigned>::min() == 0;
}
