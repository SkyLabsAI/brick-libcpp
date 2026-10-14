/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
// A call to vector::erase with the past-the-end iterator.
//
// This is undefined behavior: erase(q) requires "q denotes a valid
// dereferenceable constant iterator to a" ([sequence.reqmts]), and end() is
// not dereferenceable. _GLIBCXX_DEBUG reports it; ASan does not.
// erase_ub_proof.v shows that the erase spec in vector/spec.v rejects it;
// erase_ub_proof.expected records where the proof gets stuck.
// Its UB-free twin erases the last element in TestErase in test.cpp.
#include <vector>

void erase_end() {
    std::vector<int> v;
    v.push_back(1);
    std::vector<int>::iterator e = v.end();
    std::vector<int>::const_iterator last = e;
    v.erase(last);
}
