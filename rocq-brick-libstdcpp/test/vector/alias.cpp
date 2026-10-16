/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cstddef>
#include <vector>

// These clients have no assertions that could mask an incorrect contract value.
void
AliasAppend(std::vector<int>& v) {
    v.push_back(v[0]);
}

void
AliasFill(std::vector<int>& v, std::size_t n) {
    v.resize(n, v[1]);
}
