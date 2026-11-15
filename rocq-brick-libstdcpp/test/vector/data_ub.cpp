/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
// Accesses through vector::data() outside the elements.
//
// These are undefined behavior: data() points to the vector's elements
// ([vector.data]), and reading past them is an out-of-bounds access
// ([expr.add]/4), as is dereferencing the null data() of an empty vector
// ([expr.unary.op]/1). ASan reports both.
// data_ub_proof.v shows that the vector specs reject each one;
// data_ub_proof.expected records where the proofs get stuck.
// Their UB-free twins are in TestDataEmpty in test.cpp.
#include <vector>

int data_past_end() {
    std::vector<int> v;
    v.push_back(1);
    return v.data()[v.size()];
}

int data_empty() {
    std::vector<int> v;
    return *v.data();
}
