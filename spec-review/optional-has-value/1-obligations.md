# Requirements — bool std::optional<int>::has_value() const

Authored by three independent agents (blind to each other), audited by a fourth,
merged by a fifth. 15 requirements. Every one carries a C++20 N4861 citation and a
rationale in the full set; only the statements are reproduced here.

13 are required and map to client scenarios. 2 are deferred, with reasons.

## Core

**REQ_CORE_001** — For std::optional<int>, has_value() is a const member observer whose result is a real bool: it returns true if and only if the object currently contains an int value and false if and only if it currently contains no value. The result reports engagement only; it neither derives presence from the contained int nor changes the optional's state.

**REQ_CORE_002** — A default-constructed std::optional<int> and a std::optional<int> constructed from std::nullopt both contain no value, so has_value() returns false for each.

**REQ_CORE_003** — A std::optional<int> directly constructed from an int value, such as std::optional<int>{5}, contains a value, so has_value() returns true.

## Composition

**REQ_COMPOSITION_001** — After reset() is called on an engaged std::optional<int>, the optional contains no value and a subsequent has_value() returns false.

**REQ_COMPOSITION_002** — After a successful emplace(v) on a disengaged std::optional<int>, the optional contains a value and a subsequent has_value() returns true.

**REQ_COMPOSITION_003** — A successful emplace(v) on an already engaged std::optional<int> replaces the contained value and leaves the optional engaged, so has_value() is true afterward.

**REQ_COMPOSITION_004** — Calling reset() on a std::optional<int> that is already disengaged has no effect on engagement; repeated reset() calls leave has_value() false.

**REQ_COMPOSITION_005** — Move-constructing a std::optional<int> destination from an engaged source produces an engaged destination and leaves the moved-from source engaged; only its contained int is moved from.

**REQ_COMPOSITION_006** — Assigning std::nullopt to an engaged std::optional<int> disengages it, so a subsequent has_value() returns false.

**REQ_COMPOSITION_007** — Assigning an int value to a disengaged std::optional<int> engages it, so a subsequent has_value() returns true.

**REQ_COMPOSITION_008** — Copy construction preserves a std::optional<int>'s engagement state: copying an engaged source yields an engaged destination, and copying a disengaged source yields a disengaged destination.

## Boundary

**REQ_BOUNDARY_001** — Engagement is independent of the stored int's truth value: std::optional<int>{0} contains a value, so has_value() returns true rather than treating zero as absence.

**REQ_BOUNDARY_002** — After emplace(0) on a std::optional<int>, the optional is engaged and has_value() returns true, independent of the zero value and independent of whether the optional was already engaged.

## Rare — deferred

**REQ_RARE_001** — has_value() is usable in a constexpr compile-time evaluation context, for example in a static_assert on a constexpr std::optional<int>.

**REQ_RARE_002** — If constructing the contained value throws during emplace(args...), the optional is left disengaged afterward and any previously contained value has already been destroyed.
