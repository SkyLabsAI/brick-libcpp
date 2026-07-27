#include <cassert>
#include <cstdint>
#include <optional>

void empty_construct_has_value_false() {
    std::optional<std::uint8_t> o{std::nullopt};
    static_assert(noexcept(o.has_value()));
    assert(o.has_value() == false);
}

void value_construct_read_five() {
    const std::optional<std::uint8_t> o{std::uint8_t{5}};
    assert(o.has_value() == true);
    assert(static_cast<int>(*o) == 5);
}

void check_named_lvalue_roundtrip(std::uint8_t b) {
    const std::optional<std::uint8_t> o{b};
    assert(o.has_value() == true);
    assert(*o == b);
}

void named_lvalue_parameterized_roundtrip() {
    std::uint8_t b{37};
    check_named_lvalue_roundtrip(b);

    // Keep a literal-pinned, directly exercised instance for the execution
    // oracle as well as the parameterized client above.
    const std::optional<std::uint8_t> o{b};
    assert(o.has_value() == true);
    assert(static_cast<int>(*o) == 37);
}

// Value construction takes a snapshot of the source byte. The optional does
// not retain an alias to the named lvalue passed to its constructor.
void lvalue_source_snapshot_survives_mutation() {
    std::uint8_t source{23};
    std::optional<std::uint8_t> o{source};
    const std::optional<std::uint8_t>& view{o};

    assert(view.has_value() == true);
    assert(static_cast<int>(*view) == 23);

    source = std::uint8_t{91};
    assert(static_cast<int>(source) == 91);
    assert(view.has_value() == true);
    assert(static_cast<int>(*view) == 23);
}

void zero_byte_is_value() {
    const std::optional<std::uint8_t> o{std::uint8_t{0}};
    assert(o.has_value() == true);
    assert(static_cast<int>(*o) == 0);
}

void byte_one_and_max_are_preserved() {
    const std::optional<std::uint8_t> o_one{std::uint8_t{1}};
    const std::optional<std::uint8_t> o_max{std::uint8_t{255}};

    assert(o_one.has_value() == true);
    assert(o_max.has_value() == true);
    assert(static_cast<int>(*o_one) == 1);
    assert(static_cast<int>(*o_max) == 255);

    assert(static_cast<int>(*o_max) == 255);
    assert(static_cast<int>(*o_one) == 1);
}

void guarded_read() {
    const std::optional<std::uint8_t> empty{std::nullopt};
    assert(empty.has_value() == false);

    const std::optional<std::uint8_t> present{std::uint8_t{5}};
    assert(present.has_value() == true);
    if (present.has_value()) {
        assert(static_cast<int>(*present) == 5);
    } else {
        assert(false && "engaged optional must take the has_value branch");
    }
}

// The selected object's state is not fixed until this function receives its
// argument. has_value() is what makes the dereference branch safe; the literal
// assertions also make an always-true or always-false engagement result fail.
void check_runtime_selected_optional(bool choose_present) {
    std::optional<std::uint8_t> present{std::uint8_t{5}};
    std::optional<std::uint8_t> empty{std::nullopt};
    const std::optional<std::uint8_t>* selected{&empty};

    if (choose_present) {
        selected = &present;
    }

    if (selected->has_value()) {
        assert(selected->has_value() == true);
        assert(choose_present == true);
        assert(static_cast<int>(**selected) == 5);
    } else {
        assert(selected->has_value() == false);
        assert(choose_present == false);
    }
}

void has_value_drives_runtime_selected_deref() {
    check_runtime_selected_optional(true);
    check_runtime_selected_optional(false);
}

void two_independent_instances() {
    const std::optional<std::uint8_t> present{std::uint8_t{5}};
    const std::optional<std::uint8_t> absent{std::nullopt};

    assert(present.has_value() == true);
    assert(static_cast<int>(*present) == 5);
    assert(absent.has_value() == false);

    assert(absent.has_value() == false);
    assert(static_cast<int>(*present) == 5);
    assert(present.has_value() == true);
}

void repeated_observation_stable() {
    const std::optional<std::uint8_t> engaged{std::uint8_t{5}};
    const std::optional<std::uint8_t> empty{std::nullopt};

    assert(engaged.has_value() == true);
    assert(engaged.has_value() == true);
    assert(static_cast<int>(*engaged) == 5);
    assert(static_cast<int>(*engaged) == 5);
    assert(empty.has_value() == false);
    assert(empty.has_value() == false);
}

void check_present_by_const_ref(
    const std::optional<std::uint8_t>& o
) {
    assert(o.has_value() == true);
    if (o.has_value()) {
        assert(static_cast<int>(*o) == 5);
    } else {
        assert(false && "engaged optional must take the has_value branch");
    }
}

void check_empty_by_const_ref(
    const std::optional<std::uint8_t>& o
) {
    assert(o.has_value() == false);
}

void const_ref_parameter_read() {
    const std::optional<std::uint8_t> engaged{std::uint8_t{5}};
    const std::optional<std::uint8_t> empty{std::nullopt};

    check_present_by_const_ref(engaged);
    check_empty_by_const_ref(empty);
}

void scoped_local_lifetime() {
    int observed_byte{-1};
    bool observed_empty{false};

    {
        const std::optional<std::uint8_t> engaged{std::uint8_t{5}};
        std::optional<std::uint8_t> empty{std::nullopt};

        assert(engaged.has_value() == true);
        assert(static_cast<int>(*engaged) == 5);
        assert(empty.has_value() == false);

        observed_byte = static_cast<int>(*engaged);
        observed_empty = (empty.has_value() == false);
    }

    // These assertions run only after both optionals have left scope and their
    // destructors have completed, so scope exit has an observable continuation.
    assert(observed_byte == 5);
    assert(observed_empty == true);
}
