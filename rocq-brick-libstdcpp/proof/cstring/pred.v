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

(** [object_bytesR byte_ty q bytes] is an abstract counted byte view of an
    object range. The payload is the unsigned-byte values observed by the
    memory functions; [byte_ty] records the one-byte pointer-stepping type used
    for returned interior pointers. *)
Axiom object_bytesR : forall `{Σ : cpp_logic} {σ : genv},
  type -> cQp.t -> list Z -> Rep.

Axiom object_bytesR_cfrac : forall `{Σ : cpp_logic} {σ : genv} byte_ty bytes,
  CFractional (fun q => object_bytesR byte_ty q bytes).
#[global] Existing Instance object_bytesR_cfrac.

#[global] Instance object_bytesR_as_cfrac `{Σ : cpp_logic, σ : genv}
    byte_ty q bytes :
  AsCFractional (object_bytesR byte_ty q bytes)
    (fun q => object_bytesR byte_ty q bytes) q.
Proof. solve_as_cfrac. Qed.

(** [object_bytes_anyR byte_ty q n] owns an [n]-byte destination range at
    permission [q] whose previous byte values are irrelevant. Specs for
    mutating functions may still require [q = 1$m]. *)
Axiom object_bytes_anyR : forall `{Σ : cpp_logic} {σ : genv},
  type -> cQp.t -> Z -> Rep.

Axiom object_bytesR_to_arrayLR : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty q hi bytes,
  lengthZ bytes = hi ->
  p |-> object_bytesR ty q bytes ⊢
  p |-> arrayLR ty 0 hi (fun b : Z => ucharR q b) bytes.

Axiom object_bytesR_of_arrayLR : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty q hi bytes,
  lengthZ bytes = hi ->
  p |-> arrayLR ty 0 hi (fun b : Z => ucharR q b) bytes ⊢
  p |-> object_bytesR ty q bytes.

Axiom object_bytes_anyR_of_anyR_array : forall `{Σ : cpp_logic} {σ : genv}
    (p : ptr) ty q n,
  p |-> anyR (Tarray ty n) q ⊢
  p |-> object_bytes_anyR ty q (Z.of_N n).

Lemma borrow_arrayR_cstringR `{Σ : cpp_logic, σ : genv}
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

Lemma borrow_arrayLR_cstringR `{Σ : cpp_logic, σ : genv}
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

Lemma arrayR_ucharR_object_bytesR `{Σ : cpp_logic, σ : genv}
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

Lemma object_bytesR_half_split `{Σ : cpp_logic, σ : genv}
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

Lemma object_bytesR_prefix_tail0 `{Σ : cpp_logic, σ : genv}
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

Lemma object_bytesR_ucharR_anyR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar q xs ⊢
  p |-> anyR (Tarray Tuchar n) q.
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_to_arrayLR p Tuchar q (Z.of_N n) xs
    ltac:(apply lengthZ_of_to_nat_length; exact Hlen)
    with "Hs") as "Hs".
  iApply (arrayLR_ucharR_anyR with "Hs").
  exact Hlen.
Qed.

Lemma object_bytesR_ucharR_object_bytes_anyR
    `{Σ : cpp_logic, σ : genv} (p : ptr) q n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar q xs ⊢
  p |-> object_bytes_anyR Tuchar q (Z.of_N n).
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_ucharR_anyR _ q n xs Hlen with "Hs") as "Hs".
  iApply (object_bytes_anyR_of_anyR_array with "Hs").
Qed.

Lemma object_bytesR_ucharR_arrayR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q xs :
  p |-> object_bytesR Tuchar q xs ⊢
  p |-> arrayR Tuchar (fun b : Z => ucharR q b) xs.
Proof.
  iIntros "Hs".
  iPoseProof (object_bytesR_to_arrayLR p Tuchar q (lengthZ xs) xs
    eq_refl with "Hs") as "Hs".
  rewrite arrayLR.unlock _at_sep.
  iDestruct "Hs" as "[_ Hs]".
  rewrite _at_offsetR _at_sub_0; [iExact "Hs"|done].
Qed.

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

Lemma object_bytesR_ucharR_arrayLR_anyR
    `{Σ : cpp_logic, σ : genv} (p : ptr) q n xs :
  N.to_nat n = length xs ->
  p |-> object_bytesR Tuchar q xs ⊢
  p |-> arrayLR Tuchar 0 (Z.of_N n)
    (fun _ : unit => anyR Tuchar q) (replicateN n ()).
Proof.
  intros Hlen.
  iIntros "Hs".
  iPoseProof (object_bytesR_ucharR_arrayR p q xs with "Hs") as "Hs".
  rewrite arrayLR.unlock _at_sep.
  iSplit.
  - iPureIntro.
    unfold lengthZ, lengthN, replicateN.
    rewrite length_replicate N2Nat.id.
    lia.
  - rewrite _at_offsetR _at_sub_0; [|done].
    rewrite -(N2Nat.id n) Hlen.
    iApply (arrayR_ucharR_arrayR_anyR with "Hs").
Qed.

Lemma object_bytesR_arrayLR_cons `{Σ : cpp_logic, σ : genv}
    (p : ptr) x xs :
  p |-> object_bytesR Tuchar 1$m (x :: xs) ⊣⊢
  (type_ptr Tuchar (p .[Tuchar ! 0]) ∗ p .[Tuchar ! 0] |-> ucharR 1$m x) ∗
  p |-> arrayLR Tuchar 1 (lengthZ (x :: xs)) (fun b : Z => ucharR 1$m b) xs.
Proof.
  iSplit.
  - iIntros "Hs".
    iPoseProof (object_bytesR_to_arrayLR p Tuchar 1$m (lengthZ (x :: xs))
      (x :: xs) eq_refl with "Hs") as "Hs".
    iEval (rewrite (arrayLR_cons p 0 (lengthZ (x :: xs))
      (fun b : Z => ucharR 1$m b) x xs)) in "Hs".
    iExact "Hs".
  - iIntros "[[#Hty Hx] Hs]".
    iApply (object_bytesR_of_arrayLR p Tuchar 1$m (lengthZ (x :: xs))
      (x :: xs) eq_refl).
    rewrite (arrayLR_cons p 0 (lengthZ (x :: xs))
      (fun b : Z => ucharR 1$m b) x xs).
    iFrame "# ∗".
Qed.

Lemma uchar_cells_object_bytesR_two `{Σ : cpp_logic, σ : genv}
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
  rewrite (at_arrayR_ucharR_cons p 1$m a [b]).
  iFrame "Hty0 Ha".
  rewrite (at_arrayR_ucharR_cons (p .[Tuchar ! 1]) 1$m b []).
  iFrame "Hty1 Hb".
  rewrite arrayR_nil _at_sep.
  iSplit.
  - iApply (at_type_ptrR_validR_plus_one with "Hty1").
  - iPureIntro. done.
Qed.

Lemma arrayR_ucharR_anyR `{Σ : cpp_logic, σ : genv} (p : ptr) n xs :
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
