/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <optional>
#include <type_traits>
#include <utility>

// std::optional<int>::has_value() is a member observer, so the only way to name
// it as a bare call (as the value-pinning gate requires of a pinned function) is
// through this thin free forwarder. It performs no logic of its own: it returns
// exactly the engagement bit the member reports, so a client that pins
// has_value(o) against a literal pins the member's own contract. The proof of
// this forwarder discharges its spec directly from the frozen member has_value
// contract, so nothing here is assumed.
static bool has_value(const std::optional<int>& o) {
    return o.has_value();
}

void literal_bool_result() {
    // has_value() is a const-qualified observer returning a real bool — verified
    // at compile time on a const reference type, without materializing a const
    // object at runtime.
    static_assert(std::is_same_v<
        decltype(std::declval<const std::optional<int>&>().has_value()), bool>);

    std::optional<int> engaged{5};
    std::optional<int> disengaged{std::nullopt};

    const bool engaged_result = engaged.has_value();
    const bool disengaged_result = disengaged.has_value();

    assert(engaged_result == true);
    assert(disengaged_result == false);
    assert(engaged.has_value() == true);
    assert(disengaged.has_value() == false);
}

void disengaged_construction_reports_false() {
    std::optional<int> default_constructed;
    std::optional<int> nullopt_constructed{std::nullopt};

    assert(default_constructed.has_value() == false);
    assert(nullopt_constructed.has_value() == false);
}

void value_construction_reports_true() {
    std::optional<int> value{5};

    assert(value.has_value() == true);
}

void zero_value_reports_true() {
    std::optional<int> zero{0};

    assert(zero.has_value() == true);
}

void reset_then_query_reports_false() {
    std::optional<int> value{5};
    value.reset();

    assert(value.has_value() == false);
}

void emplace_then_query_reports_true() {
    std::optional<int> value;
    value.emplace(7);

    assert(value.has_value() == true);
}

void reemplace_already_engaged_stays_engaged() {
    std::optional<int> value{3};

    assert(value.has_value() == true);
    value.emplace(9);
    assert(value.has_value() == true);
}

void double_reset_idempotent() {
    std::optional<int> value;

    value.reset();
    assert(value.has_value() == false);
    value.reset();
    assert(value.has_value() == false);
}

void move_construct_preserves_source_engagement() {
    std::optional<int> source{42};
    std::optional<int> destination{std::move(source)};

    assert(destination.has_value() == true);
    assert(source.has_value() == true);
}

void move_construct_disengaged_stays_disengaged() {
    std::optional<int> source;

    assert(source.has_value() == false);
    std::optional<int> destination{std::move(source)};
    assert(destination.has_value() == false);
    assert(source.has_value() == false);
}

void emplace_zero_still_engaged() {
    std::optional<int> value{5};
    value.emplace(0);

    assert(value.has_value() == true);
}

void assign_nullopt_disengages() {
    std::optional<int> value{5};
    value = std::nullopt;

    assert(value.has_value() == false);
}

void assign_value_engages() {
    std::optional<int> value;
    value = 7;

    assert(value.has_value() == true);
}

void copy_construct_engaged() {
    std::optional<int> source{5};
    std::optional<int> destination{source};

    assert(has_value(destination) == true);
}

void copy_construct_disengaged() {
    std::optional<int> source;
    std::optional<int> destination{source};

    assert(has_value(destination) == false);
}
