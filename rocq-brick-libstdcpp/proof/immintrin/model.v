(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import Stdlib.ZArith.BinInt.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.list.

(** * Pure Gallina model of 256-bit AVX2 byte-vector operations *)

Definition vec256_wf (bs : list N) : Prop :=
  length bs = 32%nat /\ List.Forall (fun b => (b < 256)%N) bs.

Definition sbyte_of_N (b : N) : Z :=
  if bool_decide (b < 128)%N then Z.of_N b else (Z.of_N b - 256)%Z.

Definition avx2_set1_epi8 (b : N) : list N :=
  repeat (b mod 256)%N 32%nat.

Definition avx2_cmpeq_epi8 (a b : list N) : list N :=
  zip_with (fun x y => if bool_decide (x = y) then 255%N else 0%N) a b.

Definition avx2_sub_epi8 (a b : list N) : list N :=
  zip_with (fun x y => ((x + 256 - y mod 256) mod 256)%N) a b.

Definition avx2_cmpgt_epi8 (a b : list N) : list N :=
  zip_with
    (fun x y =>
       if bool_decide (sbyte_of_N (x mod 256) > sbyte_of_N (y mod 256))%Z
       then 255%N
       else 0%N)
    a b.

Definition avx2_or_si256 (a b : list N) : list N :=
  zip_with N.lor a b.

Fixpoint movemask_bytes (bs : list N) : N :=
  match bs with
  | [] => 0%N
  | b :: rest =>
      if N.testbit b 7
      then (2 * movemask_bytes rest + 1)%N
      else (2 * movemask_bytes rest)%N
  end.

Definition avx2_movemask_epi8 (bs : list N) : N :=
  movemask_bytes bs.

(** * Well-formedness and bit-level characterization lemmas *)

Lemma Forall_repeat_lt256 (b : N) (k : nat) :
  (b < 256)%N ->
  List.Forall (fun x => (x < 256)%N) (repeat b k).
Proof.
  intros Hb.
  induction k as [|k IH]; simpl; constructor; assumption.
Qed.

Lemma vec256_wf_set1 (b : N) :
  vec256_wf (avx2_set1_epi8 b).
Proof.
  split.
  - unfold avx2_set1_epi8. apply repeat_length.
  - unfold avx2_set1_epi8. apply Forall_repeat_lt256.
    apply N.mod_lt. lia.
Qed.

Lemma avx2_set1_epi8_small (b : N) :
  (b < 256)%N ->
  avx2_set1_epi8 b = repeat b 32%nat.
Proof.
  intros Hb. unfold avx2_set1_epi8.
  rewrite N.mod_small; [reflexivity | exact Hb].
Qed.

Lemma zip_with_length_gen {A B C : Type} (f : A -> B -> C) (a : list A) (b : list B) :
  length (zip_with f a b) = Nat.min (length a) (length b).
Proof.
  revert b.
  induction a as [|x xs IH]; intros [|y ys]; simpl;
    [reflexivity | reflexivity | reflexivity |].
  f_equal. apply IH.
Qed.

Lemma lookup_zip_with_gen {A B C : Type} (f : A -> B -> C)
    (a : list A) (b : list B) (i : nat) :
  zip_with f a b !! i =
  match a !! i, b !! i with
  | Some x, Some y => Some (f x y)
  | _, _ => None
  end.
Proof.
  revert b i.
  induction a as [|x xs IH]; intros [|y ys] [|i]; simpl; try reflexivity.
  - destruct (xs !! i); reflexivity.
  - apply IH.
Qed.

Lemma zip_with_cmpeq_bounds (a b : list N) :
  List.Forall (fun x => (x < 256)%N) (avx2_cmpeq_epi8 a b).
Proof.
  unfold avx2_cmpeq_epi8.
  revert b.
  induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
  - case_bool_decide; lia.
  - apply IH.
Qed.

Lemma vec256_wf_cmpeq (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_cmpeq_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_cmpeq_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - apply zip_with_cmpeq_bounds.
Qed.

Lemma vec256_wf_sub (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_sub_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_sub_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_sub_epi8.
    clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
    + apply N.mod_lt. lia.
    + apply IH.
Qed.

Lemma vec256_wf_cmpgt (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_cmpgt_epi8 a b).
Proof.
  intros [Hlena _] [Hlenb _].
  split.
  - unfold avx2_cmpgt_epi8. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_cmpgt_epi8.
    clear Hlena Hlenb. revert b.
    induction a as [|x xs IH]; intros [|y ys]; simpl; try constructor.
    + case_bool_decide; lia.
    + apply IH.
Qed.

Lemma N_lor_lt_256 (x y : N) :
  (x < 256)%N ->
  (y < 256)%N ->
  (N.lor x y < 256)%N.
Proof.
  change 256%N with (2 ^ 8)%N.
  intros Hx Hy.
  destruct (N.eq_dec (N.lor x y) 0%N) as [-> | Hnz]; [lia |].
  apply N.log2_lt_pow2; [lia |].
  rewrite N.log2_lor.
  apply N.max_lub_lt.
  - destruct (N.eq_dec x 0%N) as [-> | Hx0]; [simpl; lia |].
    apply N.log2_lt_pow2; [lia | exact Hx].
  - destruct (N.eq_dec y 0%N) as [-> | Hy0]; [simpl; lia |].
    apply N.log2_lt_pow2; [lia | exact Hy].
Qed.

Lemma vec256_wf_or (a b : list N) :
  vec256_wf a ->
  vec256_wf b ->
  vec256_wf (avx2_or_si256 a b).
Proof.
  intros [Hlena Hba] [Hlenb Hbb].
  split.
  - unfold avx2_or_si256. rewrite zip_with_length_gen Hlena Hlenb. reflexivity.
  - unfold avx2_or_si256.
    clear Hlena Hlenb.
    revert b Hbb.
    induction Hba as [|x xs Hx Hxs IH]; intros [|y ys] Hbb; simpl; try constructor.
    + inversion Hbb; subst.
      exact (N_lor_lt_256 x y Hx H1).
    + inversion Hbb; subst.
      exact (IH ys H2).
Qed.

Lemma movemask_bytes_bound (bs : list N) :
  (movemask_bytes bs < 2 ^ N.of_nat (length bs))%N.
Proof.
  induction bs as [|b rest IH]; simpl.
  - lia.
  - replace (N.of_nat (S (length rest))) with (1 + N.of_nat (length rest))%N by lia.
    rewrite N.pow_add_r /=.
    destruct (N.testbit b 7); lia.
Qed.

Lemma avx2_movemask_epi8_bound (bs : list N) :
  vec256_wf bs ->
  (avx2_movemask_epi8 bs < 2 ^ 32)%N.
Proof.
  intros [Hlen _].
  unfold avx2_movemask_epi8.
  pose proof (movemask_bytes_bound bs) as Hbound.
  rewrite Hlen in Hbound.
  exact Hbound.
Qed.

Lemma avx2_movemask_epi8_testbit (bs : list N) (i : nat) :
  N.testbit (avx2_movemask_epi8 bs) (N.of_nat i) =
  match bs !! i with
  | Some b => N.testbit b 7
  | None => false
  end.
Proof.
  unfold avx2_movemask_epi8.
  revert i.
  induction bs as [|b rest IH]; intros [|i]; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (N.testbit b 7).
    + apply N.testbit_odd_0.
    + apply N.testbit_even_0.
  - rewrite Nat2N.inj_succ.
    destruct (N.testbit b 7).
    + rewrite N.testbit_odd_succ; [apply IH | lia].
    + rewrite N.testbit_even_succ; [apply IH | lia].
Qed.

Lemma lookup_repeat_lt {A : Type} (x : A) (n i : nat) :
  (i < n)%nat ->
  repeat x n !! i = Some x.
Proof.
  revert i.
  induction n as [|n IH]; intros [|i] Hi; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Theorem avx2_movemask_cmpeq_set1_bit_spec (bs : list N) (needle : N) (i : nat) :
  vec256_wf bs ->
  (needle < 256)%N ->
  (i < 32)%nat ->
  N.testbit (avx2_movemask_epi8 (avx2_cmpeq_epi8 bs (avx2_set1_epi8 needle))) (N.of_nat i) =
  bool_decide (bs !! i = Some needle).
Proof.
  intros [Hlen _] Hneedle Hi.
  rewrite avx2_movemask_epi8_testbit /avx2_cmpeq_epi8 lookup_zip_with_gen.
  rewrite (avx2_set1_epi8_small needle Hneedle).
  rewrite (lookup_repeat_lt needle 32 i Hi).
  destruct (lookup_lt_is_Some_2 bs i ltac:(lia)) as [b Hb].
  rewrite Hb.
  case_bool_decide as Heq.
  - subst b. rewrite bool_decide_eq_true_2; [reflexivity | reflexivity].
  - rewrite bool_decide_eq_false_2; [reflexivity | congruence].
Qed.

(** Signed-byte modular bias identity used for range classification
    (e.g. classifying [0x60..0x7f] via [_mm256_sub_epi8] and [_mm256_cmpgt_epi8]). *)
Lemma avx2_signed_bias_range_0x60_0x7f (b : N) :
  (b < 256)%N ->
  bool_decide
    (sbyte_of_N (0xa0 mod 256) >
     sbyte_of_N (((b + 256 - 0xe0 mod 256) mod 256) mod 256))%Z =
  bool_decide (0x60 <= b <= 0x7f)%N.
Proof.
  intros Hb.
  change (0xa0 mod 256)%N with 160%N.
  change (0xe0 mod 256)%N with 224%N.
  rewrite N.Div0.mod_mod.
  replace (sbyte_of_N 160) with (-96)%Z by reflexivity.
  destruct (N.lt_ge_cases b 224) as [Hlt224 | Hge224].
  - replace (b + 256 - 224)%N with (b + 32)%N by lia.
    rewrite (N.mod_small (b + 32)%N 256%N ltac:(lia)).
    unfold sbyte_of_N.
    repeat case_bool_decide; try reflexivity; lia.
  - replace (b + 256 - 224)%N with ((b - 224) + 1 * 256)%N by lia.
    rewrite N.Div0.mod_add.
    rewrite (N.mod_small (b - 224)%N 256%N ltac:(lia)).
    unfold sbyte_of_N.
    repeat case_bool_decide; try reflexivity; lia.
Qed.

Succeed Example ex_movemask_set1_high :
  avx2_movemask_epi8 (avx2_set1_epi8 0x80) = 0xffffffff%N := eq_refl.
Succeed Example ex_movemask_set1_low :
  avx2_movemask_epi8 (avx2_set1_epi8 0x7f) = 0%N := eq_refl.
