/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <optional>

// A default-constructed optional is disengaged. A contract that licenses this
// assertion has lost the required relationship between state and has_value().
void bad_default_optional_reports_true() {
    std::optional<int> value;

    assert(value.has_value() == true);
}
