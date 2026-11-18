/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <array>

// Clients of the [std.array] laws: the dataclass model, const transport, folding
// element-wise ownership after value initialization, and the non-member
// comparisons. See <<laws_cpp_proof.v>>.

using namespace std;

/* --- a std::array as a dataclass field -------------------------------------- */

struct Holder {
    array<unsigned char, 16> bytes;
    unsigned tag;
};

unsigned char
HolderByte(const Holder& h, unsigned long i) {
    return h.bytes[i];
}

/* --- a const std::array local ---------------------------------------------- */

unsigned char
ConstLocal() {
    const array<unsigned char, 4> a{1, 2, 3, 4};
    return a[2];
}

/* --- value initialization followed by a member call ------------------------ */

unsigned char
ZeroThenFill(unsigned char v) {
    array<unsigned char, 16> a{};
    a.fill(v);
    return a[3];
}

/* --- non-member comparisons ------------------------------------------------- */

bool
Eq(const array<unsigned char, 16>& a, const array<unsigned char, 16>& b) {
    return a == b;
}

// In C++20 <<a != b>> is rewritten to <<!(a == b)>>.
bool
Ne(const array<int, 3>& a, const array<int, 3>& b) {
    return a != b;
}

int
main() {
    return 0;
}
