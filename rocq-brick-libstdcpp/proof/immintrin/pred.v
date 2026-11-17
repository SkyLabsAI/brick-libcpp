(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.immintrin.model.

(** * Vector types, alignment, and cast roundtrip lemmas for [<immintrin.h>] *)

Abbreviation Tm256i := (Tvector Tlonglong 4 32).
Abbreviation Tm256i_u := (Tvector Tlonglong 4 1).

Lemma vec256_has_type_prop {σ : genv} (bs : list N) :
  vec256_wf bs ->
  has_type_prop (σ:=σ) (Vvec bs) Tm256i.
Proof.
  intros [Hlen Hbounds].
  apply has_vector_type; [lia | rewrite Hlen; reflexivity | exact Hbounds].
Qed.

#[local] Transparent to_signed trim.

Lemma to_signed_W32_has_type_prop {σ : genv} (z : Z) :
  has_type_prop (σ:=σ) (Vint (to_signed bitsize.W32 z)) Tint.
Proof.
  apply has_int_type.
  unfold int_rank.bound, bitsize.bound, bitsize.min_val, bitsize.max_val,
    to_signed, to_signed_bits.
  cbn -[Z.modulo Z.pow].
  pose proof (Z.mod_pos_bound z (2 ^ 32)%Z ltac:(lia)).
  case_bool_decide; lia.
Qed.

Lemma to_unsigned_to_signed_W32 (m : N) :
  (m < 2 ^ 32)%N ->
  trim 32 (to_signed bitsize.W32 (Z.of_N m)) = Z.of_N m.
Proof.
  intros Hm.
  have HmZ : (0 <= Z.of_N m < 2 ^ 32)%Z by lia.
  destruct (Z.lt_ge_cases (Z.of_N m) (2 ^ 31)%Z) as [Hlow | Hhigh].
  - rewrite (to_signed_id (Z.of_N m) bitsize.W32 ltac:(cbn; lia)).
    exact (to_unsigned_id (Z.of_N m) bitsize.W32 HmZ).
  - rewrite to_signed_eq.
    rewrite (to_signed_bits_spec_high 32 (Z.of_N m) ltac:(lia) ltac:(cbn; lia)).
    by Arith.arith_solve.
Qed.

Lemma align_of_m256i {σ : genv} :
  align_of (σ:=σ) Tm256i = Some 32%N.
Proof.
  apply (align_of_vector Tlonglong 4 32 32).
  - reflexivity.
  - lia.
  - exists 5%N. reflexivity.
  - exists 1%N. lia.
Qed.

Lemma align_of_m256i_u {σ : genv} :
  align_of (σ:=σ) Tm256i_u = Some 1%N.
Proof.
  apply (align_of_vector Tlonglong 4 1 32).
  - reflexivity.
  - lia.
  - exists 0%N. reflexivity.
  - exists 32%N. lia.
Qed.

Lemma aligned_ptr_ty_uchar_m256i_u {σ : genv} (p : ptr) :
  aligned_ptr_ty (σ:=σ) Tuchar p ->
  aligned_ptr_ty (σ:=σ) Tm256i_u p.
Proof.
  unfold aligned_ptr_ty.
  rewrite align_of_uchar align_of_m256i_u.
  intros (al & Hal & Hp).
  inversion Hal; subst al.
  exists 1%N. split; [reflexivity | exact Hp].
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma aligned_ofR_uchar_m256i_u (p : ptr) :
    p |-> aligned_ofR Tuchar |-- p |-> aligned_ofR Tm256i_u.
  Proof.
    rewrite !aligned_ofR_aligned_ptr_ty.
    f_equiv.
    exact (aligned_ptr_ty_uchar_m256i_u p).
  Qed.

  Lemma has_type_ptr_m256i_u (p : ptr) :
    has_type (Vptr p) (Tptr Tuchar) |--
    has_type (Vptr p) (Tptr Tm256i_u).
  Proof.
    by rewrite !has_type_ptr !_at_sep -aligned_ofR_uchar_m256i_u.
  Qed.
  Definition has_type_ptr_m256i_u_B := [BWD] has_type_ptr_m256i_u.

  Lemma has_type_ptr_const_m256i_u (p : ptr) :
    has_type (Vptr p) (Tptr Tuchar) |--
    has_type (Vptr p) (Tptr (Qconst Tm256i_u)).
  Proof.
    rewrite (has_type_erase_qualifiers (Tptr (Qconst Tm256i_u))) /=.
    exact (has_type_ptr_m256i_u p).
  Qed.
  Definition has_type_ptr_const_m256i_u_B := [BWD] has_type_ptr_const_m256i_u.
End with_cpp.

#[global] Hint Resolve
  vec256_wf_set1
  vec256_wf_cmpeq
  vec256_wf_sub
  vec256_wf_cmpgt
  vec256_wf_or
  avx2_movemask_epi8_bound
  vec256_has_type_prop
  to_signed_W32_has_type_prop : pure sl_opacity has_type_prop.
#[global] Hint Resolve
  has_type_ptr_m256i_u_B
  has_type_ptr_const_m256i_u_B : sl_opacity.
