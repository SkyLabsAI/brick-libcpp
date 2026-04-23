(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.anyR.
(** BEGIN: SKYLABS DEFAULT PROOF IMPORTS *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.cpp.array.
Import expr_join.
#[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
#[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.
(** END: SKYLABS DEFAULT PROOF IMPORTS *)
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Import skylabs.brick.libstdcpp.test.cstring.test_cpp.

Import normalize.only_provable_norm.

Import normalize.normalize_ptr.
Import refine_lib.

#[local] Lemma borrow_arrayR_cstringR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q bytes s tail :
  bytes = cstring.to_zstring s ++ tail ->
  cstring.WF s ->
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c)
          bytes ⊢
  p |-> cstring.R q s ∗
  (p |-> cstring.R q s -∗
   p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c)
           bytes).
Proof.
  intros Hbytes Hwf.
  subst bytes.
  rewrite (arrayR_app (fun c : N => charR q c) (Tchar_ char_type.Cchar)).
  iIntros "[Hs Htail]".
  iSplitL "Hs".
  - rewrite /cstring.R /zstring.R. iFrame. done.
  - iIntros "Hs".
    rewrite /cstring.R /zstring.R.
    iDestruct "Hs" as "[Hs _]".
    iFrame.
Qed.

#[local] Lemma borrow_arrayLR_cstringR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q bytes s tail :
  bytes = cstring.to_zstring s ++ tail ->
  cstring.WF s ->
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ bytes)
          (fun c : N => charR q c) bytes ⊢
  p |-> cstring.R q s ∗
  (p |-> cstring.R q s -∗
   p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ bytes)
           (fun c : N => charR q c) bytes).
Proof.
  intros Hbytes Hwf.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  iPoseProof (borrow_arrayR_cstringR p q bytes s tail Hbytes Hwf with "Harr")
    as "[Hs Hclose]".
  iSplitL "Hs".
  - iExact "Hs".
  - iIntros "Hs".
    iPoseProof ("Hclose" with "Hs") as "Harr".
    rewrite /arrayLR.
    iSplit.
    + iPureIntro. lia.
    + iExact "Harr".
Qed.

#[local] Lemma offset_entails `{Σ : cpp_logic, σ : genv}
    (o : offset) (P Q : Rep) :
  (P ⊢ Q) -> o |-> P ⊢ o |-> Q.
Proof.
  intros HPQ. apply _offsetR_mono. exact HPQ.
Qed.

#[local] Lemma at_zero_intro `{Σ : cpp_logic, σ : genv}
    (p : ptr) (R : Rep) :
  p |-> R ⊢ p .[Tuchar ! 0] |-> R.
Proof.
  rewrite _at_sub_0; [reflexivity|done].
Qed.

#[local] Lemma at_zero_elim `{Σ : cpp_logic, σ : genv}
    (p : ptr) (R : Rep) :
  p .[Tuchar ! 0] |-> R ⊢ p |-> R.
Proof.
  rewrite _at_sub_0; [reflexivity|done].
Qed.

#[local] Lemma at_type_ptrR_validR_plus_one `{Σ : cpp_logic, σ : genv}
    (p : ptr) ty :
  p |-> type_ptrR ty ⊢ p .[ty ! 1] |-> validR.
Proof.
  rewrite -_at_offsetR.
  apply heap_pred._at_cancel.
  apply type_ptrR_validR_plus_one.
Qed.

#[local] Lemma at_uchar_offset_add_intro `{Σ : cpp_logic, σ : genv}
    (p : ptr) i j k (R : Rep) :
  k = (i + j)%Z ->
  p .[Tuchar ! k] |-> R ⊢ p .[Tuchar ! i] .[Tuchar ! j] |-> R.
Proof.
  intros ->.
  rewrite o_sub_sub.
  reflexivity.
Qed.

#[local] Lemma at_uchar_offset_add_elim `{Σ : cpp_logic, σ : genv}
    (p : ptr) i j k (R : Rep) :
  k = (i + j)%Z ->
  p .[Tuchar ! i] .[Tuchar ! j] |-> R ⊢ p .[Tuchar ! k] |-> R.
Proof.
  intros ->.
  rewrite o_sub_sub.
  reflexivity.
Qed.

#[local] Lemma arrayR_charR_Vchar `{Σ : cpp_logic, σ : genv} q xs :
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

#[local] Lemma at_arrayR_charR_Vchar `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
  p |-> arrayR (Tchar_ char_type.Cchar)
          (fun c : N => primR (Tchar_ char_type.Cchar) q (Vchar c)) xs.
Proof.
  apply heap_pred._at_cancel.
  by apply arrayR_charR_Vchar.
Qed.

#[local] Lemma arrayR_charR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
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

#[local] Lemma arrayLR_charR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
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

#[local] Lemma at_charR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q x :
  p |-> charR q x ⊢ p |-> anyR (Tchar_ char_type.Cchar) q.
Proof.
  apply heap_pred._at_cancel.
  apply primR_anyR.
Qed.

#[local] Lemma arrayR_charR_arrayR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) xs :
  p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR 1$m c) xs ⊢
  p |-> arrayR (Tchar_ char_type.Cchar)
         (fun _ : unit => anyR (Tchar_ char_type.Cchar) 1$m)
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

#[local] Lemma arrayLR_charR_arrayLR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (Z.of_N n)
         (fun c : N => charR 1$m c) xs ⊢
  p |-> arrayLR (Tchar_ char_type.Cchar) 0 (Z.of_N n)
         (fun _ : unit => anyR (Tchar_ char_type.Cchar) 1$m)
         (replicateN n ()).
Proof.
  intros Hlen.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  replace (replicateN n ()) with (replicateN (lengthN xs) ())
    by (rewrite /replicateN /lengthN -(N2Nat.id n) Hlen; reflexivity).
  iPoseProof (arrayR_charR_arrayR_anyR with "Harr") as "Harr".
  rewrite /arrayLR.
  iSplit.
  - iPureIntro.
    unfold lengthZ, lengthN, replicateN.
    rewrite length_replicate.
    replace (length xs) with (N.to_nat n) by exact Hlen.
    repeat rewrite N2Nat.id.
    lia.
  - rewrite _at_offsetR _at_sub_0; [|done].
    iExact "Harr".
Qed.

#[local] Lemma arrayLR_prefix_tail0 `{Σ : cpp_logic, σ : genv}
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

#[local] Lemma arrayR_ucharR_object_bytesR `{Σ : cpp_logic, σ : genv}
    (p : ptr) xs :
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs ⊢
  p |-> object_bytesR Tuchar 1$m xs.
Proof.
  iIntros "Hs".
  iApply object_bytesR_of_arrayLR; [reflexivity|].
  rewrite arrayLR.unlock _at_sep.
  iSplit; [iPureIntro; lia|].
  rewrite _at_offsetR _at_sub_0; [iExact "Hs"|done].
Qed.

#[local] Lemma object_bytesR_half_split `{Σ : cpp_logic, σ : genv}
    (p : ptr) ty bytes :
  p |-> object_bytesR ty 1$m bytes ⊣⊢
  p |-> object_bytesR ty (cQp.mk false (1/2)) bytes ∗
  p |-> object_bytesR ty (cQp.mk false (1/2)) bytes.
Proof.
  rewrite -(cfractional (P := fun q => p |-> object_bytesR ty q bytes)
    (cQp.mk false (1/2)) (cQp.mk false (1/2))).
  rewrite -cQp.mk_add' Qp.half_half.
  reflexivity.
Qed.

#[local] Lemma object_bytesR_prefix_tail0 `{Σ : cpp_logic, σ : genv}
    (p : ptr) ty q mid hi xs0 xs1 :
  lengthZ (xs0 ++ xs1) = hi ->
  lengthZ xs0 = mid ->
  lengthZ xs1 = (hi - mid)%Z ->
  p |-> object_bytesR ty q (xs0 ++ xs1) ⊣⊢
  p |-> object_bytesR ty q xs0 ∗
  p .[ty ! mid] |-> object_bytesR ty q xs1.
Proof.
  intros Htotal Hhead Htail.
  iSplit.
  - iIntros "Hs".
    iPoseProof (object_bytesR_to_arrayLR p ty q hi (xs0 ++ xs1)
      Htotal with "Hs") as "Hs".
    iPoseProof (arrayLR_prefix_tail0 p ty mid hi
      (fun b : Z => ucharR q b) xs0 xs1
      ltac:(rewrite <- Hhead; rewrite N2Z.id; reflexivity)
      ltac:(lia) ltac:(lia) with "Hs") as "[Hhead Htail]".
    iPoseProof (object_bytesR_of_arrayLR p ty q mid xs0
      Hhead with "Hhead") as "Hhead".
    iPoseProof (object_bytesR_of_arrayLR (p .[ ty ! mid]) ty q
      (hi - mid) xs1 Htail with "Htail") as "Htail".
    iFrame.
  - iIntros "[Hhead Htail]".
    iPoseProof (object_bytesR_to_arrayLR p ty q mid xs0
      Hhead with "Hhead") as "Hhead".
    iPoseProof (object_bytesR_to_arrayLR (p .[ ty ! mid]) ty q
      (hi - mid) xs1 Htail with "Htail") as "Htail".
    iPoseProof ((arrayLR_prefix_tail0 p ty mid hi
      (fun b : Z => ucharR q b) xs0 xs1
      ltac:(rewrite <- Hhead; rewrite N2Z.id; reflexivity)
      ltac:(lia) ltac:(lia)) with "[$Hhead $Htail]") as "Hs".
    iPoseProof (object_bytesR_of_arrayLR p ty q hi
      (xs0 ++ xs1) Htotal with "Hs") as "Hs".
    iExact "Hs".
Qed.

#[local] Lemma arrayLR_ucharR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> arrayLR Tuchar 0 (Z.of_N n) (fun c : Z => ucharR 1$m c) xs ⊢
  p |-> anyR (Tarray Tuchar n) 1$m.
Proof.
  intros Hlen.
  rewrite arrayLR.unlock _at_sep.
  iIntros "[_ Harr]".
  rewrite _at_offsetR _at_sub_0; [|done].
  rewrite anyR_array.
  iApply (arrayR_anyR_f (fun c : Z => c) with "Harr").
  exact Hlen.
Qed.

#[local] Lemma lengthZ_of_to_nat_length {A : Type} (n : N) (xs : list A) :
  N.to_nat n = length xs -> lengthZ xs = Z.of_N n.
Proof.
  intros Hlen.
  unfold lengthZ, lengthN.
  rewrite <- Hlen, N2Nat.id.
  reflexivity.
Qed.

#[local] Lemma memchr_found_after_prefix prefix b suffix c :
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

#[local] Lemma memchr_missing_if_no_match bytes c :
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

#[local] Ltac solve_memchr_side :=
  unfold byte_of_int;
  repeat (rewrite Z.mod_small; [|lia]);
  match goal with
  | |- List.Forall _ [] => constructor
  | |- List.Forall _ (_ :: _) =>
      constructor; [solve_memchr_side | solve_memchr_side]
  | |- _ => lia
  end.

#[local] Lemma object_bytesR_ucharR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar 1$m xs ⊢
  p |-> anyR (Tarray Tuchar n) 1$m.
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_to_arrayLR p Tuchar 1$m (Z.of_N n) xs
    ltac:(apply lengthZ_of_to_nat_length; exact Hlen)
    with "Hs") as "Hs".
  iApply (arrayLR_ucharR_anyR with "Hs").
  exact Hlen.
Qed.

#[local] Lemma object_bytesR_ucharR_object_bytes_anyR
    `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar 1$m xs ⊢
  p |-> object_bytes_anyR Tuchar (Z.of_N n).
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_ucharR_anyR _ n xs Hlen with "Hs") as "Hs".
  iApply (object_bytes_anyR_of_anyR_array with "Hs").
Qed.

#[local] Lemma object_bytesR_ucharR_arrayR `{Σ : cpp_logic, σ : genv}
    (p : ptr) xs :
  p |-> object_bytesR Tuchar 1$m xs ⊢
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs.
Proof.
  iIntros "Hs".
  iPoseProof (object_bytesR_to_arrayLR p Tuchar 1$m (lengthZ xs) xs
    eq_refl with "Hs") as "Hs".
  rewrite arrayLR.unlock _at_sep.
  iDestruct "Hs" as "[_ Hs]".
  rewrite _at_offsetR _at_sub_0; [iExact "Hs"|done].
Qed.

#[local] Lemma at_arrayR_ucharR_cons `{Σ : cpp_logic, σ : genv}
    (p : ptr) x xs :
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) (x :: xs) ⊣⊢
  p |-> type_ptrR Tuchar ∗
  p |-> ucharR 1$m x ∗
  p .[Tuchar ! 1] |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs.
Proof.
  rewrite arrayR_cons !_at_sep.
  rewrite _at_offsetR.
  reflexivity.
Qed.

#[local] Lemma at_arrayR_cons `{Σ : cpp_logic, σ : genv}
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

#[local] Lemma at_ucharR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q x :
  p |-> ucharR q x ⊢ p |-> anyR Tuchar q.
Proof.
  apply heap_pred._at_cancel.
  apply primR_anyR.
Qed.

#[local] Lemma arrayR_ucharR_arrayR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) xs :
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs ⊢
  p |-> arrayR Tuchar (fun _ : unit => anyR Tuchar 1$m)
    (replicateN (lengthN xs) ()).
Proof.
  revert p.
  induction xs as [|x xs IH].
  all: intros p.
  - rewrite /lengthN /= !arrayR_nil. reflexivity.
  - rewrite (at_arrayR_ucharR_cons p x xs).
    iIntros "(Hty & Hx & Hxs)".
    replace (lengthN (x :: xs)) with (N.succ (lengthN xs)) by
      (rewrite /lengthN Nat2N.inj_succ; reflexivity).
    rewrite replicateN_S.
    rewrite (at_arrayR_cons p Tuchar
      (fun _ : unit => anyR Tuchar 1$m) () (replicateN (lengthN xs) ())).
    iFrame "Hty".
    iSplitL "Hx".
    + iApply (at_ucharR_anyR with "Hx").
    + iApply (IH with "Hxs").
Qed.

#[local] Lemma object_bytesR_ucharR_arrayLR_anyR
    `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar 1$m xs ⊢
  p |-> arrayLR Tuchar 0 (Z.of_N n)
    (fun _ : unit => anyR Tuchar 1$m) (replicateN n ()).
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_ucharR_arrayR with "Hs") as "Hs".
  rewrite arrayLR.unlock _at_sep.
  iSplit.
  - iPureIntro.
    unfold lengthZ, lengthN, replicateN.
    rewrite length_replicate N2Nat.id.
    lia.
  - 
  rewrite _at_offsetR _at_sub_0; [|done].
  rewrite -(N2Nat.id n) Hlen.
  iApply (arrayR_ucharR_arrayR_anyR with "Hs").
Qed.

#[local] Lemma uchar_cells_object_bytesR_two `{Σ : cpp_logic, σ : genv}
    (p : ptr) a b :
  p |-> ucharR 1$m a ∗
  p .[Tuchar ! 1] |-> ucharR 1$m b ⊢
  p |-> object_bytesR Tuchar 1$m [a; b].
Proof.
  iIntros "(Ha & Hb)".
  iDestruct (observe (p |-> type_ptrR Tuchar) with "Ha") as "#Hty0".
  iDestruct (observe (p .[Tuchar ! 1] |-> type_ptrR Tuchar) with "Hb")
    as "#Hty1".
  iApply arrayR_ucharR_object_bytesR.
  rewrite (at_arrayR_ucharR_cons p a [b]).
  iFrame "Hty0 Ha".
  rewrite (at_arrayR_ucharR_cons (p .[Tuchar ! 1]) b []).
  iFrame "Hty1 Hb".
  rewrite arrayR_nil _at_sep.
  iSplit.
  - iApply (at_type_ptrR_validR_plus_one with "Hty1").
  - iPureIntro. done.
Qed.

#[local] Lemma arrayR_ucharR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
  N.to_nat n = length xs ->
  p |-> arrayR Tuchar (fun b : Z => ucharR 1$m b) xs ⊢
  p |-> anyR (Tarray Tuchar n) 1$m.
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (arrayR_ucharR_object_bytesR with "Hs") as "Hs".
  iApply (object_bytesR_ucharR_anyR with "Hs").
  exact Hlen.
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  (* Restored after the byte-array slice landed. This note records why these
     proofs were parked temporarily during focused iteration. *)

  cpp.spec "test_strlen()" default.
  Lemma test_strlen_ok : verify[module] "test_strlen()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strlen_embedded_null()" default.
  Lemma test_strlen_embedded_null_ok :
    verify[module] "test_strlen_embedded_null()".
  Admitted.

  cpp.spec "test_strcmp()" default.
  Lemma test_strcmp_ok : verify[module] "test_strcmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcmp_embedded_null()" default.
  Lemma test_strcmp_embedded_null_ok :
    verify[module] "test_strcmp_embedded_null()".
  Admitted.

  cpp.spec "test_strncmp()" default.
  Lemma test_strncmp_ok : verify[module] "test_strncmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strncmp_embedded_null()" default.
  Lemma test_strncmp_embedded_null_ok :
    verify[module] "test_strncmp_embedded_null()".
  Admitted.

  cpp.spec "test_strlen_array_buffer()" default.
  Lemma test_strlen_array_buffer_ok :
    verify[module] "test_strlen_array_buffer()".
  Proof.
    verify_spec; go.
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [99%N; 100%N; 0%N]) "ab"%bs
      [99%N; 100%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hs Hclose]".
    iExists _, "ab"%bs. iFrame "Hs".
    iSplit; [go|].
    iIntros "Hs".
    iPoseProof ("Hclose" with "Hs") as "Harr".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 6%N
      (cstring.to_zstring "ab"%bs ++ [99%N; 100%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harr")
      as "Harr".
    go.
    iFrame "Harr".
    go.
  Qed.

  cpp.spec "test_strcmp_array_buffer()" default.
  Lemma test_strcmp_array_buffer_ok :
    verify[module] "test_strcmp_array_buffer()".
  Proof.
    verify_spec; go.
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) "ab"%bs
      [120%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [121%N; 0%N]) "ab"%bs
      [121%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hy Hclosey]".
    iExists _, "ab"%bs, _, "ab"%bs. iFrame "Hx Hy".
    iIntros "[Hx Hy]".
    iPoseProof ("Hclosex" with "Hx") as "Harrx".
    iPoseProof ("Hclosey" with "Hy") as "Harry".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harrx")
      as "Harrx".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [121%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harry")
      as "Harry".
    go.
    iFrame "Harrx Harry".
    go.
  Qed.

  cpp.spec "test_strncmp_array_buffer()" default.
  Lemma test_strncmp_array_buffer_ok :
    verify[module] "test_strncmp_array_buffer()".
  Proof.
    verify_spec; go.
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) "ab"%bs
      [120%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [121%N; 0%N]) "ab"%bs
      [121%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hy Hclosey]".
    iExists _, "ab"%bs, _, "ab"%bs. iFrame "Hx Hy".
    iIntros "[Hx Hy]".
    iPoseProof ("Hclosex" with "Hx") as "Harrx".
    iPoseProof ("Hclosey" with "Hy") as "Harry".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harrx")
      as "Harrx".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [121%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harry")
      as "Harry".
    go.
    iFrame "Harrx Harry".
    go.
  Qed.

  cpp.spec "test_strchr()" default.
  Lemma test_strchr_ok : verify[module] "test_strchr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strrchr()" default.
  Lemma test_strrchr_ok : verify[module] "test_strrchr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strspn()" default.
  Lemma test_strspn_ok : verify[module] "test_strspn()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcspn()" default.
  Lemma test_strcspn_ok : verify[module] "test_strcspn()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strpbrk()" default.
  Lemma test_strpbrk_ok : verify[module] "test_strpbrk()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strstr()" default.
  Lemma test_strstr_ok : verify[module] "test_strstr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_search_embedded_null_array_buffer()" default.
  Lemma test_search_embedded_null_array_buffer_ok :
    verify[module] "test_search_embedded_null_array_buffer()".
  Proof using MOD.
    verify_spec; go.
    iPoseProof (borrow_arrayLR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [98%N; 99%N; 0%N]) "ab"%bs
      [98%N; 99%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hs Hclose]".
    iExists _, "ab"%bs. iFrame "Hs".
    iIntros "Hs".
    go.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go.
    go.
    Arith.arith_simpl; go.
    go.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "Hs".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "Hs".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "Hs".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "Hs".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Haccept]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hreject]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hneedle]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hneedle_b]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hneedle_bc]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hneedle_b2]".
    Arith.arith_simpl; go; ego.
    iSplitL "Hs"; [iExact "Hs"|].
    iIntros "[Hs Hempty]".
    Arith.arith_simpl; go; ego.
    iPoseProof ("Hclose" with "Hs") as "Harr".
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 6%N
      (cstring.to_zstring "ab"%bs ++ [98%N; 99%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harr")
      as "Harr".
    go.
    iFrame "Harr".
    go.
  Qed.

  cpp.spec "test_cstring_slice1()" default.
  Lemma test_cstring_slice1_ok : verify[module] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_memset()" default.
  Lemma test_memset_ok : verify[module] "test_memset()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (s_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]) as "Hs".
    iPoseProof (object_bytesR_of_arrayLR s_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hs") as "Hs".

    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Htarget Htail]".
    iExists Tuchar.
    iSplitL "Htarget".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 2%N
        [97%Z; 98%Z] ltac:(reflexivity) with "Htarget").
    - iIntros "Htarget".
      go.
      iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
        (cQp.mk false 1) 2 4 [120%Z; 120%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Htarget $Htail]") as "Hs".
      iPoseProof (object_bytesR_ucharR_arrayR with "Hs") as "Hs".
      rewrite (at_arrayR_ucharR_cons s_addr 120%Z
        [120%Z; 99%Z; 100%Z]).
      iDestruct "Hs" as "[#Hty0 [H0 Hs]]".
      iPoseProof (at_zero_intro s_addr with "H0") as "H0".
      iExists (Vint 120%Z), (cQp.mk false 1%Qp).
      iFrame "H0". iIntros "H0".
      go.
      iPoseProof (at_arrayR_ucharR_cons (s_addr .[Tuchar ! 1])
        120%Z [99%Z; 100%Z] with "Hs") as "Hs".
      iDestruct "Hs" as "[#Hty1 [H1 Hs]]".
      iExists (Vint 120%Z), (cQp.mk false 1%Qp).
      iFrame "H1". iIntros "H1".
      go.
      iPoseProof (at_arrayR_ucharR_cons
        (s_addr .[Tuchar ! 1] .[Tuchar ! 1])
        99%Z [100%Z] with "Hs") as "Hs".
      iDestruct "Hs" as "[#Hty2 [H2 Hs]]".
      iEval (rewrite o_sub_sub) in "H2".
      iEval (rewrite o_sub_sub) in "Hs".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "H2". iIntros "H2".
      go.
      iPoseProof (at_arrayR_ucharR_cons
        (s_addr .[Tuchar ! 1] .[Tuchar ! 2])
        100%Z [] with "Hs") as "Hs".
      iDestruct "Hs" as "[#Hty3 [H3 Hs]]".
      iEval (rewrite o_sub_sub) in "H3".
      iEval (rewrite o_sub_sub) in "Hs".
      Arith.arith_simpl.
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "H3". iIntros "H3".
      go.
      iPoseProof (at_zero_elim s_addr with "H0") as "H0".
      iPoseProof (uchar_cells_object_bytesR_two s_addr 120%Z 120%Z
        with "[$H0 $H1]") as "Hhead".
      Arith.arith_simpl.
      iPoseProof (at_uchar_offset_add_intro s_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "H3") as "H3".
      iPoseProof (uchar_cells_object_bytesR_two (s_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$H2 $H3]") as "Htail".
      iPoseProof (object_bytesR_prefix_tail0 (s_addr .[ Tuchar ! 2])
        Tuchar (cQp.mk false 1) 1 2 [99%Z] [100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Htail")
        as "[Htarget Htail]".
      iRename "Hs" into "Hempty".
      go.
      go.
      iExists Tuchar.
      iSplitL "Htarget".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 1%N
          [99%Z] ltac:(reflexivity) with "Htarget").
      + iIntros "Htarget".
        go.
        iPoseProof ((object_bytesR_prefix_tail0 (s_addr .[ Tuchar ! 2])
          Tuchar (cQp.mk false 1) 1 2 [35%Z] [100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Htarget $Htail]") as "Htail".
        iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
          (cQp.mk false 1) 2 4 [120%Z; 120%Z] [35%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hhead $Htail]") as "Hs".
        iPoseProof (object_bytesR_ucharR_arrayR with "Hs") as "Hs".
        go.
        rewrite (at_arrayR_ucharR_cons s_addr 120%Z
          [120%Z; 35%Z; 100%Z]).
        iDestruct "Hs" as "[#Hty0' [H0 Hs]]".
        iPoseProof (at_zero_intro s_addr with "H0") as "H0_assert".
        iPoseProof (at_arrayR_ucharR_cons (s_addr .[Tuchar ! 1])
          120%Z [35%Z; 100%Z] with "Hs") as "Hs".
        iDestruct "Hs" as "[#Hty1' [H1 Hs]]".
        iPoseProof (at_arrayR_ucharR_cons
          (s_addr .[Tuchar ! 1] .[Tuchar ! 1])
          35%Z [100%Z] with "Hs") as "Hs".
        iDestruct "Hs" as "[#Hty2' [H2 Hs]]".
        iEval (rewrite o_sub_sub) in "H2".
        iEval (rewrite o_sub_sub) in "Hs".
        Arith.arith_simpl.
        iExists (Vint 35%Z), (cQp.mk false 1%Qp).
        iFrame "H2". iIntros "H2".
        go.
        iPoseProof (at_arrayR_ucharR_cons
          (s_addr .[Tuchar ! 1] .[Tuchar ! 2])
          100%Z [] with "Hs") as "Hs".
        iDestruct "Hs" as "[#Hty3' [H3 Hempty2]]".
        iEval (rewrite o_sub_sub) in "H3".
        Arith.arith_simpl.
        iExists (Vint 100%Z), (cQp.mk false 1%Qp).
        iFrame "H3". iIntros "H3".
        go.
        iPoseProof (at_zero_elim s_addr with "H0_assert") as "H0".
        iPoseProof (uchar_cells_object_bytesR_two s_addr 120%Z 120%Z
          with "[$H0 $H1]") as "Hhead".
        iPoseProof (at_uchar_offset_add_intro s_addr 2 1 3
          (ucharR 1$m 100%Z) ltac:(lia) with "H3") as "H3".
        iPoseProof (uchar_cells_object_bytesR_two (s_addr .[Tuchar ! 2])
          35%Z 100%Z with "[$H2 $H3]") as "Htail".
        iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
          (cQp.mk false 1) 2 4 [120%Z; 120%Z] [35%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hhead $Htail]") as "Hs".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [120%Z; 120%Z; 35%Z; 100%Z] ltac:(reflexivity) with "Hs")
          as "Hs".
        iFrame "Hs".
        go.
  Qed.

  cpp.spec "test_memchr()" default.
  Lemma test_memchr_ok : verify[module] "test_memchr()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (s_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 97%Z]) as "Hs".
    iPoseProof (object_bytesR_of_arrayLR s_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 97%Z] ltac:(reflexivity) with "Hs") as "Hs".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit.
      + done.
      + iIntros "Hs".
        rewrite (memchr_found_after_prefix (@nil Z) 97%Z [98%Z; 99%Z; 97%Z] 97%Z); [|solve_memchr_side..].
        Arith.arith_simpl; go.
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [97%Z; 98%Z] 99%Z [97%Z] 99%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iFrame|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_missing_if_no_match [97%Z; 98%Z; 99%Z; 97%Z] 122%Z); [|solve_memchr_side..].
    go.
    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 0 4 [] [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Hempty Hs]".
    iExists Tuchar, (cQp.mk false 1), [].
    iSplitL "Hempty"; [iExact "Hempty"|].
    iSplit; [done|].
    iIntros "Hempty".
    go.
    iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 0 4 [] [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hempty $Hs]")
      as "Hs".
    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Hhead Hs]".
    iExists Tuchar, (cQp.mk false 1), [98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [98%Z; 99%Z] 97%Z (@nil Z) 97%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hhead $Hs]")
      as "Hs".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
      [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) with "Hs") as "Hs".
    iFrame "Hs".
    go.
    rewrite o_sub_sub in H.
    simpl in H.
    contradiction.
  Qed.

  cpp.spec "test_memchr_embedded_null()" default.
  Lemma test_memchr_embedded_null_ok :
    verify[module] "test_memchr_embedded_null()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (s_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 0%Z; 98%Z; 0%Z]) as "Hs".
    iPoseProof (object_bytesR_of_arrayLR s_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 0%Z; 98%Z; 0%Z] ltac:(reflexivity) with "Hs") as "Hs".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 0%Z; 98%Z; 0%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit.
    + done.
    + iIntros "Hs".
      rewrite (memchr_found_after_prefix [97%Z] 0%Z [98%Z; 0%Z] 0%Z); [|solve_memchr_side..].
      Arith.arith_simpl; go.
    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 2 4 [97%Z; 0%Z] [98%Z; 0%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Hhead Hs]".
    iExists Tuchar, (cQp.mk false 1), [98%Z; 0%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [98%Z] 0%Z (@nil Z) 0%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    rewrite o_sub_sub.
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 2 4 [97%Z; 0%Z] [98%Z; 0%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hhead $Hs]")
      as "Hs".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 0%Z; 98%Z; 0%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [97%Z; 0%Z] 98%Z [0%Z] 98%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
      [97%Z; 0%Z; 98%Z; 0%Z]
      ltac:(reflexivity) with "Hs") as "Hs".
    iFrame "Hs".
    go.
    rewrite o_sub_sub in H.
    simpl in H.
    contradiction.
  Qed.

  cpp.spec "test_memcpy()" default.
  Lemma test_memcpy_ok : verify[module] "test_memcpy()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (src_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]) as "Hsrc".
    iDestruct select (dst_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [119%Z; 120%Z; 121%Z; 122%Z]) as "Hdst".

    iPoseProof (object_bytesR_of_arrayLR src_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc") as "Hsrc".
    iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
      (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc")
      as "[Hsrc_copy Hsrc_tail]".

    iPoseProof (object_bytesR_of_arrayLR dst_addr Tuchar (cQp.mk false 1)
      4 [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst") as "Hdst".
    iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
      (cQp.mk false 1) 3 4 [119%Z; 120%Z; 121%Z] [122%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst")
      as "[Hdst_copy Hdst_tail]".

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iExists Tuchar.
    iSplitL "Hsrc_copy"; [iExact "Hsrc_copy"|].
    iSplitL "Hdst_copy".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 3%N
        [119%Z; 120%Z; 121%Z] ltac:(reflexivity) with "Hdst_copy").
    - iSplit; [done|].
      iIntros "[Hsrc_copy Hdst_copy]".
      Arith.arith_simpl.
      go.

      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_copy $Hsrc_tail]") as "Hsrc".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_copy $Hdst_tail]") as "Hdst".

      iPoseProof (object_bytesR_ucharR_arrayR with "Hdst") as "Hdst".
      rewrite (at_arrayR_ucharR_cons dst_addr 97%Z
        [98%Z; 99%Z; 122%Z]).
      iDestruct "Hdst" as "[#Hdst_ty0 [Hdst0 Hdst]]".
      iPoseProof (at_zero_intro dst_addr with "Hdst0") as "Hdst0".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iPoseProof (at_arrayR_ucharR_cons (dst_addr .[Tuchar ! 1])
        98%Z [99%Z; 122%Z] with "Hdst") as "Hdst".
      iDestruct "Hdst" as "[#Hdst_ty1 [Hdst1 Hdst]]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iPoseProof (at_arrayR_ucharR_cons (dst_addr .[Tuchar ! 1] .[Tuchar ! 1])
        99%Z [122%Z] with "Hdst") as "Hdst".
      iDestruct "Hdst" as "[#Hdst_ty2 [Hdst2 Hdst]]".
      iEval (rewrite o_sub_sub) in "Hdst2".
      iEval (rewrite o_sub_sub) in "Hdst".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iPoseProof (at_arrayR_ucharR_cons
        (dst_addr .[Tuchar ! 1] .[Tuchar ! 2])
        122%Z [] with "Hdst") as "Hdst".
      iDestruct "Hdst" as "[#Hdst_ty3 [Hdst3 Hdst]]".
      iEval (rewrite o_sub_sub) in "Hdst".
      Arith.arith_simpl.
      iPoseProof (at_uchar_offset_add_elim dst_addr 1 2 3
        (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iExists (Vint 122%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (object_bytesR_ucharR_arrayR with "Hsrc") as "Hsrc".
      rewrite (at_arrayR_ucharR_cons src_addr 97%Z
        [98%Z; 99%Z; 100%Z]).
      iDestruct "Hsrc" as "[#Hsrc_ty0 [Hsrc0 Hsrc]]".
      iPoseProof (at_zero_intro src_addr with "Hsrc0") as "Hsrc0".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc0". iIntros "Hsrc0".
      go.

      iPoseProof (at_arrayR_ucharR_cons (src_addr .[Tuchar ! 1])
        98%Z [99%Z; 100%Z] with "Hsrc") as "Hsrc".
      iDestruct "Hsrc" as "[#Hsrc_ty1 [Hsrc1 Hsrc]]".
      iPoseProof (at_arrayR_ucharR_cons
        (src_addr .[Tuchar ! 1] .[Tuchar ! 1])
        99%Z [100%Z] with "Hsrc") as "Hsrc".
      iDestruct "Hsrc" as "[#Hsrc_ty2 [Hsrc2 Hsrc]]".
      iPoseProof (at_arrayR_ucharR_cons
        (src_addr .[Tuchar ! 1] .[Tuchar ! 1] .[Tuchar ! 1])
        100%Z [] with "Hsrc") as "Hsrc".
      iDestruct "Hsrc" as "[#Hsrc_ty3 [Hsrc3 Hsrc]]".
      iEval (rewrite o_sub_sub) in "Hsrc2".
      iEval (rewrite o_sub_sub) in "Hsrc3".
      iEval (rewrite o_sub_sub) in "Hsrc".
      Arith.arith_simpl.
      iPoseProof (at_uchar_offset_add_elim src_addr 1 2 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hsrc3") as "Hsrc3".
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc3". iIntros "Hsrc3".
      go.

      iPoseProof (at_zero_elim src_addr with "Hsrc0") as "Hsrc0".
      iPoseProof (uchar_cells_object_bytesR_two src_addr 97%Z 98%Z
        with "[$Hsrc0 $Hsrc1]") as "Hsrc_head".
      iPoseProof (at_uchar_offset_add_intro src_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hsrc3") as "Hsrc3".
      iPoseProof (uchar_cells_object_bytesR_two (src_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$Hsrc2 $Hsrc3]") as "Hsrc_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_head $Hsrc_tail2]") as "Hsrc_full".

      iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
      iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
        with "[$Hdst0 $Hdst1]") as "Hdst_head".
      iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
        (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
        99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".

      iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc_full")
        as "[Hsrc_prefix Hsrc_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
        (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hsrc_suffix") as "[Hsrc_empty Hsrc_suffix]".

      iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst_full")
        as "[Hdst_head1 Hdst_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hdst_suffix") as "[Hdst_empty Hdst_suffix]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 0%N
          [] ltac:(reflexivity) with "Hdst_empty").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty]".
        Arith.arith_simpl.
        go.

        iPoseProof ((object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
          (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_empty $Hsrc_suffix]") as "Hsrc_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_prefix $Hsrc_suffix]") as "Hsrc_full".

        iPoseProof ((object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_empty $Hdst_suffix]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_ucharR_arrayR with "Hdst_full") as "Hdst_arr".
        rewrite (at_arrayR_ucharR_cons dst_addr 97%Z
          [98%Z; 99%Z; 122%Z]).
        iDestruct "Hdst_arr" as "[#Hdst_ty4 [Hdst0 Hdst_arr]]".
        iPoseProof (at_zero_intro dst_addr with "Hdst0") as "Hdst0".
        iExists (Vint 97%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst0". iIntros "Hdst0".
        go.

        iPoseProof (at_arrayR_ucharR_cons (dst_addr .[Tuchar ! 1])
          98%Z [99%Z; 122%Z] with "Hdst_arr") as "Hdst_arr".
        iDestruct "Hdst_arr" as "[#Hdst_ty5 [Hdst1 Hdst_arr]]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full") as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (at_arrayR_ucharR_cons
          (dst_addr .[Tuchar ! 1] .[Tuchar ! 1]) 99%Z [122%Z]))
          in "Hdst_arr".
        iDestruct "Hdst_arr" as "[#Hdst_ty6 [Hdst2 Hdst_arr]]".
        iPoseProof (at_arrayR_ucharR_cons
          (dst_addr .[Tuchar ! 1] .[Tuchar ! 1] .[Tuchar ! 1])
          122%Z [] with "Hdst_arr") as "Hdst_arr".
        iDestruct "Hdst_arr" as "[#Hdst_ty7 [Hdst3 Hdst_arr]]".
        iEval (rewrite o_sub_sub) in "Hdst2".
        iEval (rewrite o_sub_sub) in "Hdst3".
        iEval (rewrite o_sub_sub) in "Hdst3".
        iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
          (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
        iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
          99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 122%Z] ltac:(reflexivity) with "Hdst_full") as "Hdst_any".
        iFrame "Hsrc_any Hdst_any".
        go.
  Qed.

  cpp.spec "test_memmove()" default.
  Lemma test_memmove_ok : verify[module] "test_memmove()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (src_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]) as "Hsrc".
    iDestruct select (dst_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [119%Z; 120%Z; 121%Z; 122%Z]) as "Hdst".

    iPoseProof (object_bytesR_of_arrayLR src_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc") as "Hsrc".
    iPoseProof (object_bytesR_of_arrayLR dst_addr Tuchar (cQp.mk false 1)
      4 [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst") as "Hdst".

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 100%Z].
    iExists Tuchar.
    iSplitL "Hsrc"; [iExact "Hsrc"|].
    iSplitL "Hdst".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 4%N
        [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst").
    - iSplit; [done|].
      iIntros "[Hsrc Hdst]".
      Arith.arith_simpl.
      go.

      iPoseProof (object_bytesR_ucharR_arrayR with "Hdst") as "Hdst_arr".
      rewrite (at_arrayR_ucharR_cons dst_addr 97%Z
        [98%Z; 99%Z; 100%Z]).
      iDestruct "Hdst_arr" as "[#Hdst_ty0 [Hdst0 Hdst_arr]]".
      iPoseProof (at_zero_intro dst_addr with "Hdst0") as "Hdst0".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iPoseProof (at_arrayR_ucharR_cons (dst_addr .[Tuchar ! 1])
        98%Z [99%Z; 100%Z] with "Hdst_arr") as "Hdst_arr".
      iDestruct "Hdst_arr" as "[#Hdst_ty1 [Hdst1 Hdst_arr]]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iPoseProof (at_arrayR_ucharR_cons
        (dst_addr .[Tuchar ! 1] .[Tuchar ! 1])
        99%Z [100%Z] with "Hdst_arr") as "Hdst_arr".
      iDestruct "Hdst_arr" as "[#Hdst_ty2 [Hdst2 Hdst_arr]]".
      iEval (rewrite o_sub_sub) in "Hdst2".
      iEval (rewrite o_sub_sub) in "Hdst_arr".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iPoseProof (at_arrayR_ucharR_cons
        (dst_addr .[Tuchar ! 1] .[Tuchar ! 2])
        100%Z [] with "Hdst_arr") as "Hdst_arr".
      iDestruct "Hdst_arr" as "[#Hdst_ty3 [Hdst3 Hdst_arr]]".
      iEval (rewrite o_sub_sub) in "Hdst_arr".
      Arith.arith_simpl.
      iPoseProof (at_uchar_offset_add_elim dst_addr 1 2 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
      iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
        with "[$Hdst0 $Hdst1]") as "Hdst_head".
      iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".

      iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc")
        as "[Hsrc_head1 Hsrc_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hsrc_suffix") as "[Hsrc_empty Hsrc_suffix]".

      iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst_full")
        as "[Hdst_head1 Hdst_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hdst_suffix") as "[Hdst_empty Hdst_suffix]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 0%N
          [] ltac:(reflexivity) with "Hdst_empty").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty]".
        Arith.arith_simpl.
        go.

        iPoseProof ((object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_empty $Hsrc_suffix]") as "Hsrc_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_head1 $Hsrc_suffix]") as "Hsrc_full".

        iPoseProof ((object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_empty $Hdst_suffix]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_ucharR_arrayR with "Hdst_full") as "Hdst_arr2".
        rewrite (at_arrayR_ucharR_cons dst_addr 97%Z
          [98%Z; 99%Z; 100%Z]).
        iDestruct "Hdst_arr2" as "[#Hdst_ty4 [Hdst0 Hdst_arr2]]".
        iPoseProof (at_zero_intro dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (at_arrayR_ucharR_cons (dst_addr .[Tuchar ! 1])
          98%Z [99%Z; 100%Z] with "Hdst_arr2") as "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[#Hdst_ty5 [Hdst1 Hdst_arr2]]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full")
          as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (at_arrayR_ucharR_cons
          (dst_addr .[Tuchar ! 1] .[Tuchar ! 1]) 99%Z [100%Z]))
          in "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[#Hdst_ty6 [Hdst2 Hdst_arr3]]".
        iPoseProof (at_arrayR_ucharR_cons
          (dst_addr .[Tuchar ! 1] .[Tuchar ! 1] .[Tuchar ! 1])
          100%Z [] with "Hdst_arr3") as "Hdst_arr3".
        iDestruct "Hdst_arr3" as "[#Hdst_ty7 [Hdst3 Hdst_arr3]]".
        iEval (rewrite o_sub_sub) in "Hdst2".
        iEval (rewrite o_sub_sub) in "Hdst3".
        iEval (rewrite o_sub_sub) in "Hdst3".
        iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
          (ucharR 1$m 100%Z) ltac:(lia) with "Hdst3") as "Hdst3".
        iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
          99%Z 100%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hdst_full")
          as "Hdst_any".
        iFrame "Hsrc_any Hdst_any".
        go.
  Qed.

  cpp.spec "test_memcmp()" default.
  Lemma test_memcmp_ok : verify[module] "test_memcmp()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (abc_addr |-> arrayLR Tuchar 0 3
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z]) as "Habc".
    iDestruct select (abd_addr |-> arrayLR Tuchar 0 3
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 100%Z]) as "Habd".
    iDestruct select (ab_addr |-> arrayLR Tuchar 0 2
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z]) as "Hab".

    iPoseProof (object_bytesR_of_arrayLR abc_addr Tuchar (cQp.mk false 1)
      3 [97%Z; 98%Z; 99%Z] ltac:(reflexivity) with "Habc") as "Habc".
    iPoseProof (object_bytesR_half_split with "Habc") as
      "[Habc_left Habc_right]".
    iExists Tuchar, (cQp.mk false (1/2)), [97%Z; 98%Z; 99%Z].
    iExists Tuchar, (cQp.mk false (1/2)), [97%Z; 98%Z; 99%Z].
    iSplitL "Habc_left"; [iExact "Habc_left"|].
    iSplitL "Habc_right"; [iExact "Habc_right"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_left Habc_right]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_half_split abc_addr Tuchar
      [97%Z; 98%Z; 99%Z]) with "[$Habc_left $Habc_right]") as "Habc".

    iPoseProof (object_bytesR_of_arrayLR abd_addr Tuchar (cQp.mk false 1)
      3 [97%Z; 98%Z; 100%Z] ltac:(reflexivity) with "Habd") as "Habd".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 100%Z].
    iSplitL "Habc"; [iExact "Habc"|].
    iSplitL "Habd"; [iExact "Habd"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc Habd]".
    Arith.arith_simpl.
    go.

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 100%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iSplitL "Habd"; [iExact "Habd"|].
    iSplitL "Habc"; [iExact "Habc"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habd Habc]".
    Arith.arith_simpl.
    go.

    iPoseProof (object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habc")
      as "[Habc_prefix Habc_tail]".
    iPoseProof (object_bytesR_prefix_tail0 abd_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habd")
      as "[Habd_prefix Habd_tail]".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z].
    iSplitL "Habc_prefix"; [iExact "Habc_prefix"|].
    iSplitL "Habd_prefix"; [iExact "Habd_prefix"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_prefix Habd_prefix]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habc_prefix $Habc_tail]") as "Habc".
    iPoseProof ((object_bytesR_prefix_tail0 abd_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habd_prefix $Habd_tail]") as "Habd".

    iPoseProof (object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 0 3 [] [97%Z; 98%Z; 99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habc")
      as "[Habc_empty Habc]".
    iPoseProof (object_bytesR_of_arrayLR ab_addr Tuchar (cQp.mk false 1)
      2 [97%Z; 98%Z] ltac:(reflexivity) with "Hab") as "Hab".
    iPoseProof (object_bytesR_prefix_tail0 ab_addr Tuchar
      (cQp.mk false 1) 0 2 [] [97%Z; 98%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hab")
      as "[Hab_empty Hab]".
    iExists Tuchar, (cQp.mk false 1), [].
    iExists Tuchar, (cQp.mk false 1), [].
    iSplitL "Habc_empty"; [iExact "Habc_empty"|].
    iSplitL "Hab_empty"; [iExact "Hab_empty"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_empty Hab_empty]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 0 3 [] [97%Z; 98%Z; 99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habc_empty $Habc]") as "Habc".
    iPoseProof ((object_bytesR_prefix_tail0 ab_addr Tuchar
      (cQp.mk false 1) 0 2 [] [97%Z; 98%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hab_empty $Hab]") as "Hab".

    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 3%N
      [97%Z; 98%Z; 99%Z] ltac:(reflexivity) with "Habc") as "Habc".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 3%N
      [97%Z; 98%Z; 100%Z] ltac:(reflexivity) with "Habd") as "Habd".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 2%N
      [97%Z; 98%Z] ltac:(reflexivity) with "Hab") as "Hab".
    iFrame "Habc Habd Hab".
    go.
  Qed.

  cpp.spec "test_memcmp_embedded_null()" default.

  cpp.spec "test_memset_embedded_null()" default.

  cpp.spec "test_memcpy_embedded_null()" default.

  cpp.spec "test_memmove_overlap()" default.

  cpp.spec "test_memmove_embedded_null()" default.

  cpp.spec "test_cstring_slice4()" default.
End with_cpp.
