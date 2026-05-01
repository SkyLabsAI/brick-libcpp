(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.anyR.
Require Import skylabs.cpp.array.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.cstring.model.

#[local] Set Primitive Projections.

#[local] Open Scope Z_scope.

Lemma offset_entails `{Σ : cpp_logic, σ : genv}
    (o : offset) (P Q : Rep) :
  (P ⊢ Q) -> o |-> P ⊢ o |-> Q.
Proof.
  intros HPQ. apply _offsetR_mono. exact HPQ.
Qed.

Lemma at_zero_intro `{Σ : cpp_logic, σ : genv}
    (p : ptr) (R : Rep) :
  p |-> R ⊢ p .[Tuchar ! 0] |-> R.
Proof.
  rewrite _at_sub_0; [reflexivity|done].
Qed.

Lemma at_zero_elim `{Σ : cpp_logic, σ : genv}
    (p : ptr) (R : Rep) :
  p .[Tuchar ! 0] |-> R ⊢ p |-> R.
Proof.
  rewrite _at_sub_0; [reflexivity|done].
Qed.

Lemma at_type_ptrR_validR_plus_one `{Σ : cpp_logic, σ : genv}
    (p : ptr) ty :
  p |-> type_ptrR ty ⊢ p .[ty ! 1] |-> validR.
Proof.
  rewrite -_at_offsetR.
  apply heap_pred._at_cancel.
  apply type_ptrR_validR_plus_one.
Qed.

Lemma at_uchar_offset_add_intro `{Σ : cpp_logic, σ : genv}
    (p : ptr) i j k (R : Rep) :
  k = (i + j)%Z ->
  p .[Tuchar ! k] |-> R ⊢ p .[Tuchar ! i] .[Tuchar ! j] |-> R.
Proof.
  intros ->.
  rewrite o_sub_sub.
  reflexivity.
Qed.

Lemma at_uchar_offset_add_elim `{Σ : cpp_logic, σ : genv}
    (p : ptr) i j k (R : Rep) :
  k = (i + j)%Z ->
  p .[Tuchar ! i] .[Tuchar ! j] |-> R ⊢ p .[Tuchar ! k] |-> R.
Proof.
  intros ->.
  rewrite o_sub_sub.
  reflexivity.
Qed.

Lemma arrayR_charR_Vchar `{Σ : cpp_logic, σ : genv} q xs :
  arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
  arrayR (Tchar_ char_type.Cchar)
    (fun c : N => primR (Tchar_ char_type.Cchar) q (Vchar c)) xs.
Proof.
  induction xs as [| x xs IH].
  - rewrite !arrayR_nil. iIntros "[$ $]".
  - rewrite !arrayR_cons.
    iIntros "[$ [$ Hxs]]".
    iApply (offset_entails with "Hxs").
    exact IH.
Qed.

Lemma at_arrayR_charR_Vchar `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
  p |-> arrayR (Tchar_ char_type.Cchar)
          (fun c : N => primR (Tchar_ char_type.Cchar) q (Vchar c)) xs.
Proof.
  apply heap_pred._at_cancel.
  by apply arrayR_charR_Vchar.
Qed.

Lemma arrayR_charR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR 1$m c) xs ⊢
  p |-> anyR (Tarray (Tchar_ char_type.Cchar) n) 1$m.
Proof.
  intros Hlen.
  iIntros "Harr".
  iPoseProof (at_arrayR_charR_Vchar with "Harr") as "Harr".
  rewrite anyR_array.
  iApply (arrayR_anyR_f (fun c : N => Vchar c) with "Harr").
  exact Hlen.
Qed.

Lemma arrayLR_charR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (Z.of_N n)
         (fun c : N => charR 1$m c) xs ⊢
  p |-> anyR (Tarray (Tchar_ char_type.Cchar) n) 1$m.
Proof.
  intros Hlen.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  iApply (arrayR_charR_anyR with "Harr").
  exact Hlen.
Qed.

Lemma at_charR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q x :
  p |-> charR q x ⊢ p |-> anyR (Tchar_ char_type.Cchar) q.
Proof.
  apply heap_pred._at_cancel.
  apply primR_anyR.
Qed.

Lemma arrayR_charR_arrayR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
  p |-> arrayR (Tchar_ char_type.Cchar)
         (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
         (replicateN (lengthN xs) ()).
Proof.
  revert p.
  induction xs as [|x xs IH].
  all: intros p.
  - rewrite /lengthN /= !arrayR_nil. reflexivity.
  - rewrite arrayR_cons !_at_sep _at_offsetR.
    iIntros "(Hty & Hx & Hxs)".
    replace (lengthN (x :: xs)) with (N.succ (lengthN xs)) by
      (rewrite /lengthN Nat2N.inj_succ; reflexivity).
    rewrite replicateN_S.
    rewrite arrayR_cons !_at_sep _at_offsetR.
    iFrame "Hty".
    iSplitL "Hx".
    + iApply (at_charR_anyR with "Hx").
    + iApply (IH with "Hxs").
Qed.

Lemma arrayLR_charR_arrayLR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
         (fun c : N => charR q c) xs ⊢
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
         (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
         (replicateN (lengthN xs) ()).
Proof.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  iPoseProof (arrayR_charR_arrayR_anyR _ q with "Harr") as "Harr".
  rewrite /arrayLR.
  iSplit.
  - iPureIntro.
    unfold lengthZ, lengthN, replicateN.
    rewrite length_replicate.
    rewrite Nat2N.id.
    lia.
  - rewrite _at_offsetR _at_sub_0; [|done].
    iExact "Harr".
Qed.

Lemma arrayLR_prefix_tail0 `{Σ : cpp_logic, σ : genv}
    {A : Type} (p : ptr) ty mid hi (R : A -> Rep) xs0 xs1 :
  lengthN xs0 = Z.to_N mid ->
  (0 <= mid)%Z ->
  (mid <= hi)%Z ->
  p |-> arrayLR ty 0 hi R (xs0 ++ xs1) ⊣⊢
  p |-> arrayLR ty 0 mid R xs0 ∗
  p .[ty ! mid] |-> arrayLR ty 0 (hi - mid) R xs1.
Proof.
  intros Hlen Hlo Hhi.
  assert (Hlen' : lengthN xs0 = Z.to_N (mid - 0)) by
    (replace (mid - 0)%Z with mid by lia; exact Hlen).
  rewrite (arrayLR_app' p 0 mid hi R xs0 xs1 Hlen' Hlo Hhi).
  rewrite _at_sub_arrayLR.
  Arith.arith_simpl.
  reflexivity.
Qed.

Lemma arrayLR_ucharR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) q n xs :
  N.to_nat n = length xs ->
  p |-> arrayLR Tuchar 0 (Z.of_N n) (fun c : Z => ucharR q c) xs ⊢
  p |-> anyR (Tarray Tuchar n) q.
Proof.
  intros Hlen.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  rewrite anyR_array.
  iApply (arrayR_anyR_f (fun c : Z => c) with "Harr").
  exact Hlen.
Qed.

Lemma lengthZ_of_to_nat_length {A : Type} (n : N) (xs : list A) :
  N.to_nat n = length xs -> lengthZ xs = Z.of_N n.
Proof.
  intros Hlen.
  unfold lengthZ, lengthN.
  rewrite <- Hlen, N2Nat.id.
  reflexivity.
Qed.

Lemma memchr_found_after_prefix prefix b suffix c :
  List.Forall (fun x => x <> byte_of_int c) prefix ->
  b = byte_of_int c ->
  memchr (prefix ++ b :: suffix) c = Some (Z.of_nat (length prefix)).
Proof.
  intros Hprefix Hb.
  induction Hprefix as [|x prefix Hx _ IH].
  - simpl.
    rewrite bool_decide_true; [|done].
    reflexivity.
  - simpl.
    rewrite bool_decide_false; [|done].
    rewrite IH.
    simpl.
    f_equal.
    rewrite Nat2Z.inj_succ.
    rewrite Z.add_1_l.
    reflexivity.
Qed.

Lemma memchr_missing_if_no_match bytes c :
  List.Forall (fun x => x <> byte_of_int c) bytes ->
  memchr bytes c = None.
Proof.
  intros Hbytes.
  induction Hbytes as [|x bytes Hx _ IH].
  - reflexivity.
  - simpl.
    rewrite bool_decide_false; [|done].
    rewrite IH.
    reflexivity.
Qed.

Ltac solve_memchr_side :=
  unfold byte_of_int;
  repeat (rewrite Z.mod_small; [|lia]);
  match goal with
  | |- List.Forall _ [] => constructor
  | |- List.Forall _ (_ :: _) =>
      constructor; [solve_memchr_side | solve_memchr_side]
  | |- _ => lia
  end.

Lemma at_arrayR_ucharR_cons `{Σ : cpp_logic, σ : genv}
    (p : ptr) q x xs :
  p |-> arrayR Tuchar (fun b : Z => ucharR q b) (x :: xs) ⊣⊢
  p |-> type_ptrR Tuchar ∗
  p |-> ucharR q x ∗
  p .[Tuchar ! 1] |-> arrayR Tuchar (fun b : Z => ucharR q b) xs.
Proof.
  rewrite arrayR_cons !_at_sep.
  rewrite _at_offsetR.
  reflexivity.
Qed.

Lemma at_arrayR_cons `{Σ : cpp_logic, σ : genv}
    {A : Type} (p : ptr) ty (R : A -> Rep) x xs :
  p |-> arrayR ty R (x :: xs) ⊣⊢
  p |-> type_ptrR ty ∗
  p |-> R x ∗
  p .[ty ! 1] |-> arrayR ty R xs.
Proof.
  rewrite arrayR_cons !_at_sep.
  rewrite _at_offsetR.
  reflexivity.
Qed.

Lemma at_ucharR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q x :
  p |-> ucharR q x ⊢ p |-> anyR Tuchar q.
Proof.
  apply heap_pred._at_cancel.
  apply primR_anyR.
Qed.

Lemma arrayR_ucharR_arrayR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> arrayR Tuchar (fun b : Z => ucharR q b) xs ⊢
  p |-> arrayR Tuchar (fun _ : unit => anyR Tuchar q)
    (replicateN (lengthN xs) ()).
Proof.
  revert p.
  induction xs as [|x xs IH].
  all: intros p.
  - rewrite /lengthN /= !arrayR_nil. reflexivity.
  - rewrite (at_arrayR_ucharR_cons p q x xs).
    iIntros "(Hty & Hx & Hxs)".
    replace (lengthN (x :: xs)) with (N.succ (lengthN xs)) by
      (rewrite /lengthN Nat2N.inj_succ; reflexivity).
    rewrite replicateN_S.
    rewrite (at_arrayR_cons p Tuchar
      (fun _ : unit => anyR Tuchar q) () (replicateN (lengthN xs) ())).
    iFrame "Hty".
    iSplitL "Hx".
    + iApply (at_ucharR_anyR with "Hx").
    + iApply (IH with "Hxs").
Qed.

Lemma arrayR_ucharR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  n = lengthN xs ->
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs ⊢
  p |-> anyR (Tarray Tuchar n) 1$m.
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (arrayR_ucharR_arrayR_anyR with "Hs") as "Hs".
  subst n.
  work.
  rewrite arrayLR.unlock _at_sep. arith_simpl. work.
  rewrite _at_sub_0; [ rewrite lengthN_replicateN; iFrame |]; done.
Qed.
