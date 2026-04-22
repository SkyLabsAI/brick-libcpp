(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.elpi.derive.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.cstring.model_old.

#[local] Set Primitive Projections.

Module cstringz.
  Definition ab_0_cd_lit : literal_string.t :=
    {|
      literal_string.bytes :=
        PrimStringAxioms.of_list
          [Uint63Axioms.of_Z 97; Uint63Axioms.of_Z 98; Uint63Axioms.of_Z 0;
           Uint63Axioms.of_Z 99; Uint63Axioms.of_Z 100];
      literal_string.bytes_per_char := 1;
    |}.

  (** [R q s tail] owns a concrete C character array whose initial
      null-terminated byte string is [s], followed by arbitrary [tail] bytes. *)
  Definition R `{Σ : cpp_logic, σ : genv} (q : cQp.t) (s : cstring.t)
      (tail : list N) : Rep :=
    let bytes := List.app (cstring.to_zstring s) tail in
    arrayR (Tchar_ char_type.Cchar)
      (fun c : N => charR q c) bytes.

  Lemma R_cstringR `{Σ : cpp_logic, σ : genv} q s :
    R q s [] ** [| cstring.WF s |] ⊣⊢ cstring.R q s.
  Proof.
    rewrite /R /cstring.R /zstring.R.
    rewrite app_nil_r.
    iSplit; iIntros "[$ $]".
  Qed.

  Lemma cstringR_R `{Σ : cpp_logic, σ : genv} q s :
    cstring.R q s ⊢ R q s [].
  Proof.
    rewrite -R_cstringR. iIntros "[$ _]".
  Qed.

  Lemma at_cstringR_R `{Σ : cpp_logic, σ : genv} (p : ptr) q s :
    p |-> cstring.R q s ⊢ p |-> R q s [].
  Proof.
    apply heap_pred._at_cancel.
    apply cstringR_R.
  Qed.

  Lemma R_cstringR_entails `{Σ : cpp_logic, σ : genv} q s :
    cstring.WF s -> R q s [] ⊢ cstring.R q s.
  Proof.
    intros Hwf. rewrite -R_cstringR. iIntros "HR". iFrame. done.
  Qed.

  Lemma at_R_cstringR `{Σ : cpp_logic, σ : genv} (p : ptr) q s :
    cstring.WF s -> p |-> R q s [] ⊢ p |-> cstring.R q s.
  Proof.
    intros Hwf. apply heap_pred._at_cancel. by apply R_cstringR_entails.
  Qed.

  Lemma offset_entails `{Σ : cpp_logic, σ : genv} (o : offset) (P Q : Rep) :
    (P ⊢ Q) -> o |-> P ⊢ o |-> Q.
  Proof.
    intros HPQ. apply _offsetR_mono. exact HPQ.
  Qed.

  Lemma arrayR_N_to_char_R `{Σ : cpp_logic, σ : genv} q xs :
    List.Forall (fun c => (c < 2 ^ 8)%N) xs ->
    arrayR (Tchar_ char_type.Cchar)
      (fun c : N => primR (Tchar_ char_type.Cchar) q
        (N_to_char char_type.Cchar c)) xs ⊢
    arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs.
  Proof.
    induction 1 as [| x xs Hx Hxs IH].
    - rewrite !arrayR_nil. iIntros "[$ $]".
    - rewrite !arrayR_cons.
      rewrite (N_to_char_Cchar_eq _ Hx).
      iIntros "[$ [$ Hxs]]".
      iApply (offset_entails with "Hxs").
      exact IH.
  Qed.

  Lemma arrayR_R_N_to_char `{Σ : cpp_logic, σ : genv} q xs :
    List.Forall (fun c => (c < 2 ^ 8)%N) xs ->
    arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
    arrayR (Tchar_ char_type.Cchar)
      (fun c : N => primR (Tchar_ char_type.Cchar) q
        (N_to_char char_type.Cchar c)) xs.
  Proof.
    induction 1 as [| x xs Hx Hxs IH].
    - rewrite !arrayR_nil. iIntros "[$ $]".
    - rewrite !arrayR_cons.
      rewrite (N_to_char_Cchar_eq _ Hx).
      iIntros "[$ [$ Hxs]]".
      iApply (offset_entails with "Hxs").
      exact IH.
  Qed.

  Lemma string_bytesR_R `{Σ : cpp_logic, σ : genv} q lit s tail :
    literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
    List.Forall (fun c => (c < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
    string_bytesR char_type.Cchar q lit ⊢ R q s tail.
  Proof.
    intros Hbytes Hrange.
    rewrite string_bytesR.unlock /R Hbytes.
    iIntros "Ha".
    iApply (arrayR_N_to_char_R with "Ha"). exact Hrange.
  Qed.

  Lemma at_string_bytesR_R `{Σ : cpp_logic, σ : genv} (p : ptr) q lit s tail :
    literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
    List.Forall (fun c => (c < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
    p |-> string_bytesR char_type.Cchar q lit ⊢ p |-> R q s tail.
  Proof.
    intros Hbytes Hrange.
    apply heap_pred._at_cancel.
    apply string_bytesR_R; assumption.
  Qed.

  Lemma R_string_bytesR `{Σ : cpp_logic, σ : genv} q lit s tail :
    literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
    List.Forall (fun c => (c < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
    R q s tail ⊢ string_bytesR char_type.Cchar q lit.
  Proof.
    intros Hbytes Hrange.
    rewrite string_bytesR.unlock /R Hbytes.
    iIntros "Ha".
    iApply (arrayR_R_N_to_char with "Ha"). exact Hrange.
  Qed.

  Lemma at_R_string_bytesR `{Σ : cpp_logic, σ : genv} (p : ptr) q lit s tail :
    literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
    List.Forall (fun c => (c < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
    p |-> R q s tail ⊢ p |-> string_bytesR char_type.Cchar q lit.
  Proof.
    intros Hbytes Hrange.
    apply heap_pred._at_cancel.
    apply R_string_bytesR; assumption.
  Qed.

  Lemma at_string_bytesR_ab_0_cd_R `{Σ : cpp_logic, σ : genv} (p : ptr) q :
    p |-> string_bytesR char_type.Cchar q ab_0_cd_lit ⊢
    p |-> R q "ab"%bs [99%N; 100%N; 0%N].
  Proof.
    iIntros "Hlit".
    iApply (at_string_bytesR_R with "Hlit").
    - rewrite cstring.to_zstring_unfold. vm_compute.
      do 6 (constructor; [reflexivity|]); constructor.
  Qed.

  Lemma at_R_ab_0_cd_string_bytesR `{Σ : cpp_logic, σ : genv} (p : ptr) q :
    p |-> R q "ab"%bs [99%N; 100%N; 0%N] ⊢
    p |-> string_bytesR char_type.Cchar q ab_0_cd_lit.
  Proof.
    iIntros "HR".
    iApply (at_R_string_bytesR with "HR").
    - rewrite cstring.to_zstring_unfold. vm_compute.
      do 6 (constructor; [reflexivity|]); constructor.
  Qed.

  Lemma at_R_string_bytesR_free `{Σ : cpp_logic, σ : genv}
      (p : ptr) (q : Qp) lit s tail :
    literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
    List.Forall (fun c => (c < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
    □ (∀ t : Qp, p |-> string_bytesR char_type.Cchar t$c lit ={⊤}=∗ emp) -∗
    p |-> R q$c s tail ={⊤}=∗ emp.
  Proof.
    intros Hbytes Hrange.
    iIntros "#Hfree HR".
    iPoseProof (at_R_string_bytesR with "HR") as "Hlit"; [exact Hbytes|exact Hrange|].
    iApply ("Hfree" with "Hlit").
  Qed.

  Lemma at_R_ab_0_cd_free `{Σ : cpp_logic, σ : genv} (p : ptr) (q : Qp) :
    □ (∀ t : Qp,
        p |-> string_bytesR char_type.Cchar t$c ab_0_cd_lit ={⊤}=∗ emp) -∗
    p |-> R q$c "ab"%bs [99%N; 100%N; 0%N] ={⊤}=∗ emp.
  Proof.
    iIntros "#Hfree HR".
    iPoseProof (at_R_ab_0_cd_string_bytesR with "HR") as "Hlit".
    iApply ("Hfree" with "Hlit").
  Qed.

  #[only(lazy_unfold)] derive R.
End cstringz.
