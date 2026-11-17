/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cstddef>
#include <cstdint>
#include <immintrin.h>

__attribute__((target("avx2")))
inline __m256i eq_bytes(__m256i const a, __m256i const b) {
    return _mm256_cmpeq_epi8(a, b);
}

__attribute__((target("avx2")))
uint32_t match_byte_mask_32(uint8_t const *const buf, uint8_t const needle) {
    __m256i const v =
        _mm256_loadu_si256(reinterpret_cast<__m256i_u const *>(buf));
    __m256i const target = _mm256_set1_epi8(static_cast<char>(needle));
    __m256i const matches = eq_bytes(v, target);
    return static_cast<uint32_t>(_mm256_movemask_epi8(matches));
}

__attribute__((target("avx2")))
inline __m256i range_0x60_0x7f_bytes(__m256i const v) {
    __m256i const biased =
        _mm256_sub_epi8(v, _mm256_set1_epi8(static_cast<char>(0xe0)));
    __m256i const upper = _mm256_set1_epi8(static_cast<char>(0xa0));
    return _mm256_cmpgt_epi8(upper, biased);
}

__attribute__((target("avx2")))
uint32_t control_mask_32(uint8_t const *const buf) {
    __m256i const v =
        _mm256_loadu_si256(reinterpret_cast<__m256i_u const *>(buf));
    __m256i const jd = eq_bytes(v, _mm256_set1_epi8(static_cast<char>(0x5b)));
    __m256i const push = range_0x60_0x7f_bytes(v);
    __m256i const ctrl = _mm256_or_si256(jd, push);
    return static_cast<uint32_t>(_mm256_movemask_epi8(ctrl));
}

__attribute__((target("avx2")))
void scan_control_masks(
    uint8_t const *const code,
    size_t const nblocks,
    uint32_t *const out_masks) {
    size_t b = 0;
    while (b < nblocks) {
        out_masks[b] = control_mask_32(code + size_t{32} * b);
        b = b + 1;
    }
}
