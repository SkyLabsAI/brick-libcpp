(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.immintrin.model.
Require Export skylabs.brick.libstdcpp.immintrin.pred.
Require Import skylabs.brick.libstdcpp.immintrin.inc_immintrin_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** Assumed specifications for AVX2 256-bit byte/bitwise intrinsics in [<immintrin.h>]. *)

  cpp.spec "_mm256_loadu_si256(const __m256i_u *)" as mm256_loadu_si256_spec with (
    \arg{p : ptr} "__p" (Vptr p)
    \prepost{(q : cQp.t) (bs : list N)}
      p |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs)
    \require vec256_wf bs
    \post[Vvec bs] emp).

  cpp.spec "_mm256_set1_epi8(char)" as mm256_set1_epi8_spec with (
    \arg{b : N} "__b" (Vchar b)
    \require (b < 256)%N
    \post[Vvec (avx2_set1_epi8 b)] emp).

  cpp.spec "_mm256_cmpeq_epi8(__m256i, __m256i)" as mm256_cmpeq_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_cmpeq_epi8 a b)] emp).

  cpp.spec "_mm256_sub_epi8(__m256i, __m256i)" as mm256_sub_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_sub_epi8 a b)] emp).

  cpp.spec "_mm256_cmpgt_epi8(__m256i, __m256i)" as mm256_cmpgt_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_cmpgt_epi8 a b)] emp).

  cpp.spec "_mm256_or_si256(__m256i, __m256i)" as mm256_or_si256_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \arg{b : list N} "__b" (Vvec b)
    \require vec256_wf a
    \require vec256_wf b
    \post[Vvec (avx2_or_si256 a b)] emp).

  cpp.spec "_mm256_movemask_epi8(__m256i)" as mm256_movemask_epi8_spec with (
    \arg{a : list N} "__a" (Vvec a)
    \require vec256_wf a
    \post[Vint (to_signed bitsize.W32 (Z.of_N (avx2_movemask_epi8 a)))] emp).

End with_cpp.
