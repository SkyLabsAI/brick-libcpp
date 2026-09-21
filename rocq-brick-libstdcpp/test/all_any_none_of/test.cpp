/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>
#include <cassert>
#include <type_traits>

bool
is_nonzero(unsigned char byte) {
    return byte != 0;
}

bool
is_seven(unsigned char byte) {
    return byte == 7;
}

bool
is_zero(unsigned char byte) {
    return byte == 0;
}

bool
has_high_bit(unsigned char byte) {
    return byte >= 0x80;
}

static_assert(std::is_same_v<decltype(&is_nonzero),
                             bool (*)(unsigned char)>);
static_assert(std::is_same_v<decltype(&is_seven),
                             bool (*)(unsigned char)>);
static_assert(std::is_same_v<decltype(&is_zero),
                             bool (*)(unsigned char)>);
static_assert(std::is_same_v<decltype(&has_high_bit),
                             bool (*)(unsigned char)>);

void
all_of_accepts_complete_buffer() {
    const unsigned char bytes[] = {1, 2, 255};
    assert(std::all_of(bytes, bytes + 3, is_nonzero) == true);
}

void
any_of_finds_matching_byte() {
    const unsigned char bytes[] = {0, 7, 0};
    assert(std::any_of(bytes, bytes + 3, is_nonzero) == true);
}

void
none_of_accepts_cleared_buffer() {
    const unsigned char bytes[] = {0, 0, 0};
    assert(std::none_of(bytes, bytes + 3, is_nonzero) == true);
}

void
empty_range_results() {
    const unsigned char buffer[] = {9, 0, 9};
    const unsigned char* const first = buffer + 1;
    const unsigned char* const last = buffer + 1;

    assert(std::all_of(first, last, is_nonzero) == true);
    assert(std::any_of(first, last, is_nonzero) == false);
    assert(std::none_of(first, last, is_nonzero) == true);
}

void
one_past_end_empty_range_results() {
    const unsigned char buffer[] = {9, 0, 9};
    const unsigned char* const end = buffer + 3;

    assert(std::all_of(end, end, is_nonzero) == true);
    assert(std::any_of(end, end, is_nonzero) == false);
    assert(std::none_of(end, end, is_nonzero) == true);
}

void
singleton_range_results() {
    const unsigned char cleared[] = {0};
    assert(std::all_of(cleared, cleared + 1, is_nonzero) == false);
    assert(std::any_of(cleared, cleared + 1, is_nonzero) == false);
    assert(std::none_of(cleared, cleared + 1, is_nonzero) == true);

    const unsigned char set[] = {7};
    assert(std::all_of(set, set + 1, is_nonzero) == true);
    assert(std::any_of(set, set + 1, is_nonzero) == true);
    assert(std::none_of(set, set + 1, is_nonzero) == false);

    assert(std::all_of(set, set + 1, is_seven) == true);
    assert(std::any_of(set, set + 1, is_seven) == true);
    assert(std::none_of(set, set + 1, is_seven) == false);

    assert(std::all_of(set, set + 1, is_zero) == false);
    assert(std::any_of(set, set + 1, is_zero) == false);
    assert(std::none_of(set, set + 1, is_zero) == true);
}

void
all_elements_satisfy_results() {
    const unsigned char bytes[] = {1, 2, 255};

    assert(std::all_of(bytes, bytes + 3, is_nonzero) == true);
    assert(std::any_of(bytes, bytes + 3, is_nonzero) == true);
    assert(std::none_of(bytes, bytes + 3, is_nonzero) == false);
}

void
no_elements_satisfy_results() {
    const unsigned char bytes[] = {0, 0, 0};

    assert(std::all_of(bytes, bytes + 3, is_nonzero) == false);
    assert(std::any_of(bytes, bytes + 3, is_nonzero) == false);
    assert(std::none_of(bytes, bytes + 3, is_nonzero) == true);
}

void
mixed_elements_results() {
    const unsigned char ordinary[] = {1, 0, 2};
    assert(std::all_of(ordinary, ordinary + 3, is_nonzero) == false);
    assert(std::any_of(ordinary, ordinary + 3, is_nonzero) == true);
    assert(std::none_of(ordinary, ordinary + 3, is_nonzero) == false);

    const unsigned char high_bits[] = {128, 0, 255};
    assert(std::all_of(high_bits, high_bits + 3, is_nonzero) == false);
    assert(std::any_of(high_bits, high_bits + 3, is_nonzero) == true);
    assert(std::none_of(high_bits, high_bits + 3, is_nonzero) == false);

    const unsigned char match_first[] = {1, 0, 0};
    assert(std::all_of(match_first, match_first + 3, is_nonzero) == false);
    assert(std::any_of(match_first, match_first + 3, is_nonzero) == true);
    assert(std::none_of(match_first, match_first + 3, is_nonzero) == false);

    const unsigned char match_middle[] = {0, 1, 0};
    assert(std::all_of(match_middle, match_middle + 3, is_nonzero) == false);
    assert(std::any_of(match_middle, match_middle + 3, is_nonzero) == true);
    assert(std::none_of(match_middle, match_middle + 3, is_nonzero) == false);

    const unsigned char match_last[] = {0, 0, 1};
    assert(std::all_of(match_last, match_last + 3, is_nonzero) == false);
    assert(std::any_of(match_last, match_last + 3, is_nonzero) == true);
    assert(std::none_of(match_last, match_last + 3, is_nonzero) == false);

    const unsigned char fail_first[] = {0, 1, 1};
    assert(std::all_of(fail_first, fail_first + 3, is_nonzero) == false);
    assert(std::any_of(fail_first, fail_first + 3, is_nonzero) == true);
    assert(std::none_of(fail_first, fail_first + 3, is_nonzero) == false);

    const unsigned char fail_middle[] = {1, 0, 1};
    assert(std::all_of(fail_middle, fail_middle + 3, is_nonzero) == false);
    assert(std::any_of(fail_middle, fail_middle + 3, is_nonzero) == true);
    assert(std::none_of(fail_middle, fail_middle + 3, is_nonzero) == false);

    const unsigned char fail_last[] = {1, 1, 0};
    assert(std::all_of(fail_last, fail_last + 3, is_nonzero) == false);
    assert(std::any_of(fail_last, fail_last + 3, is_nonzero) == true);
    assert(std::none_of(fail_last, fail_last + 3, is_nonzero) == false);
}

void
proper_subrange_results() {
    const unsigned char cleared_payload[] = {9, 0, 0, 9};
    const unsigned char* const cleared_first = cleared_payload + 1;
    const unsigned char* const cleared_last = cleared_payload + 3;
    assert(std::all_of(cleared_first, cleared_last, is_nonzero) == false);
    assert(std::any_of(cleared_first, cleared_last, is_nonzero) == false);
    assert(std::none_of(cleared_first, cleared_last, is_nonzero) == true);

    const unsigned char set_payload[] = {0, 4, 5, 0};
    const unsigned char* const set_first = set_payload + 1;
    const unsigned char* const set_last = set_payload + 3;
    assert(std::all_of(set_first, set_last, is_nonzero) == true);
    assert(std::any_of(set_first, set_last, is_nonzero) == true);
    assert(std::none_of(set_first, set_last, is_nonzero) == false);
}

void
range_remains_unchanged_results() {
    unsigned char packet[] = {0, 128, 7, 255, 0};
    const unsigned char saved[] = {0, 128, 7, 255, 0};
    const unsigned char* const first = packet;
    const unsigned char* const last = packet + 5;
    const unsigned char* const payload_first = packet + 1;
    const unsigned char* const payload_last = packet + 4;

    (void)std::all_of(first, last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);

    (void)std::any_of(first, last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);

    (void)std::none_of(first, last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);

    (void)std::all_of(payload_first, payload_last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);

    (void)std::any_of(payload_first, payload_last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);

    (void)std::none_of(payload_first, payload_last, is_nonzero);
    assert(packet[0] == saved[0]);
    assert(packet[1] == saved[1]);
    assert(packet[2] == saved[2]);
    assert(packet[3] == saved[3]);
    assert(packet[4] == saved[4]);
}

void
boolean_result_composition_results() {
    const unsigned char bytes[] = {1, 2, 255};
    bool accept_all = false;
    bool found_match = false;
    bool reject_no_match = false;

    if (std::all_of(bytes, bytes + 3, is_nonzero)) {
        accept_all = true;
    }
    if (std::any_of(bytes, bytes + 3, is_nonzero)) {
        found_match = true;
    }
    if (!std::none_of(bytes, bytes + 3, is_nonzero)) {
        reject_no_match = true;
    }

    assert(accept_all == true);
    assert(found_match == true);
    assert(reject_no_match == true);
}

void
any_none_of_complement_crosscheck_results() {
    const unsigned char empty_storage[] = {9, 0, 9};
    const unsigned char* const empty = empty_storage + 1;
    bool any = std::any_of(empty, empty, is_nonzero);
    bool none = std::none_of(empty, empty, is_nonzero);
    assert(any != none);
    assert(any == false);
    assert(none == true);

    const unsigned char all_matching[] = {1, 2, 255};
    any = std::any_of(all_matching, all_matching + 3, is_nonzero);
    none = std::none_of(all_matching, all_matching + 3, is_nonzero);
    assert(any != none);
    assert(any == true);
    assert(none == false);

    const unsigned char none_matching[] = {0, 0, 0};
    any = std::any_of(none_matching, none_matching + 3, is_nonzero);
    none = std::none_of(none_matching, none_matching + 3, is_nonzero);
    assert(any != none);
    assert(any == false);
    assert(none == true);

    const unsigned char mixed[] = {128, 0, 255};
    any = std::any_of(mixed, mixed + 3, is_nonzero);
    none = std::none_of(mixed, mixed + 3, is_nonzero);
    assert(any != none);
    assert(any == true);
    assert(none == false);
}

void
unsigned_high_bit_predicate_results() {
    const unsigned char all_high[] = {128, 255};
    assert(std::all_of(all_high, all_high + 2, has_high_bit) == true);
    assert(std::any_of(all_high, all_high + 2, has_high_bit) == true);
    assert(std::none_of(all_high, all_high + 2, has_high_bit) == false);

    const unsigned char all_low[] = {0, 127};
    assert(std::all_of(all_low, all_low + 2, has_high_bit) == false);
    assert(std::any_of(all_low, all_low + 2, has_high_bit) == false);
    assert(std::none_of(all_low, all_low + 2, has_high_bit) == true);

    const unsigned char mixed[] = {0, 128, 255};
    assert(std::all_of(mixed, mixed + 3, has_high_bit) == false);
    assert(std::any_of(mixed, mixed + 3, has_high_bit) == true);
    assert(std::none_of(mixed, mixed + 3, has_high_bit) == false);
}
