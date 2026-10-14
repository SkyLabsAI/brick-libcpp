/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
// A call to string::erase with pos > size().
//
// This is not undefined behavior: erase throws out_of_range ([string.erase]),
// which aborts if uncaught. Exceptions are not modeled, so the erase spec in
// string/spec.v requires pos <= size() and rejects this call;
// erase_out_of_range_proof.expected records where the proof gets stuck.
// Its in-range twin is EraseAtEnd in test.cpp.
#include <string>

void erase_past_end(std::string& s) {
    s.erase(2);
}
