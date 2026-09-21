/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>

unsigned int all_of_calls = 0;
unsigned int any_of_calls = 0;
unsigned int none_of_calls = 0;

bool
counted_all_nonzero(unsigned char byte) {
    ++all_of_calls;
    return byte != 0;
}

bool
counted_any_nonzero(unsigned char byte) {
    ++any_of_calls;
    return byte != 0;
}

bool
counted_none_nonzero(unsigned char byte) {
    ++none_of_calls;
    return byte != 0;
}

void
all_of_counting_results() {
    const unsigned char bytes[] = {1, 0, 2};
    all_of_calls = 0;
    const bool result = std::all_of(bytes, bytes + 3, counted_all_nonzero);
    assert(result == false);
    assert(all_of_calls <= 3);
}

void
any_of_counting_results() {
    const unsigned char bytes[] = {0, 7, 0};
    any_of_calls = 0;
    const bool result = std::any_of(bytes, bytes + 3, counted_any_nonzero);
    assert(result == true);
    assert(any_of_calls <= 3);
}

void
none_of_counting_results() {
    const unsigned char bytes[] = {0, 7, 0};
    none_of_calls = 0;
    const bool result = std::none_of(bytes, bytes + 3, counted_none_nonzero);
    assert(result == false);
    assert(none_of_calls <= 3);
}
