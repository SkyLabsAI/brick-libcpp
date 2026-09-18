/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>

bool
partial_is_nonzero(unsigned char byte) {
    return byte != 0;
}

void
all_of_uses_partial_predicate() {
    const unsigned char bytes[] = {7, 0};
    assert(std::all_of(bytes, bytes + 2, partial_is_nonzero) == false);
}
