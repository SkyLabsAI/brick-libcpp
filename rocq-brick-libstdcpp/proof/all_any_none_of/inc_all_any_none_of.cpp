/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <algorithm>

namespace {

bool aanof_pred(unsigned char b) { return b != 0; }

[[maybe_unused]] inline bool force_all_of(const unsigned char* first, const unsigned char* last) {
  return std::all_of(first, last, &aanof_pred);
}

[[maybe_unused]] inline bool force_any_of(const unsigned char* first, const unsigned char* last) {
  return std::any_of(first, last, &aanof_pred);
}

[[maybe_unused]] inline bool force_none_of(const unsigned char* first, const unsigned char* last) {
  return std::none_of(first, last, &aanof_pred);
}

}  // namespace
