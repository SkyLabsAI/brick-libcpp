// Calls to strncmp that read past the end of a buffer.
//
// These are undefined behavior: [cstring.syn] defers to the C library, where
// "if an array is accessed beyond the end of an object, the behavior is
// undefined" (C17 7.24.1p1). Neither buffer `a` holds a NUL among its first
// `n` characters, so strncmp has to read a[1].
// strncmp_ub_proof.v shows that the strncmp spec in cstring/spec.v rejects
// each call; strncmp_ub_proof.expected records where the proofs get stuck.
#include <cstring>

int strncmp_overread_lhs() {
    char a[1] = {'a'};
    return std::strncmp(a, "a", 2);
}

int strncmp_overread_rhs() {
    char a[1] = {'a'};
    return std::strncmp("a", a, 2);
}
