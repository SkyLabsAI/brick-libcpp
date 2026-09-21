/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cstddef>

bool
symbolic_is_nonzero(unsigned char byte) {
    return byte != 0;
}

unsigned int
all_nonzero_or_flag(const unsigned char* bytes, std::size_t count, bool flag) {
    if (std::all_of(bytes, bytes + count, symbolic_is_nonzero)) {
        return 1;
    }
    return flag ? 1 : 0;
}
