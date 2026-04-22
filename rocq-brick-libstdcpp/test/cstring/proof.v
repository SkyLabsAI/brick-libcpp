(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.anyR.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Import skylabs.brick.libstdcpp.test.cstring.test_cpp.

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

#[local] Lemma offset_entails `{Σ : cpp_logic, σ : genv}
    (o : offset) (P Q : Rep) :
  (P ⊢ Q) -> o |-> P ⊢ o |-> Q.
Proof.
  intros HPQ. apply _offsetR_mono. exact HPQ.
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

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

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
    iPoseProof (borrow_arrayR_cstringR _ _
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
    iPoseProof (arrayR_charR_anyR _ 6%N
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
    iPoseProof (borrow_arrayR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) "ab"%bs
      [120%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_arrayR_cstringR _ _
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
    iPoseProof (arrayR_charR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harrx")
      as "Harrx".
    iPoseProof (arrayR_charR_anyR _ 5%N
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
    iPoseProof (borrow_arrayR_cstringR _ _
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) "ab"%bs
      [120%N; 0%N] eq_refl
      ltac:(apply cstring.WF_cons;
        [change (Byte.x61 <> Byte.x00); congruence|];
        apply cstring.WF_cons;
        [change (Byte.x62 <> Byte.x00); congruence|];
        apply cstring.WF_nil) with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_arrayR_cstringR _ _
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
    iPoseProof (arrayR_charR_anyR _ 5%N
      (cstring.to_zstring "ab"%bs ++ [120%N; 0%N])
      ltac:(rewrite cstring.to_zstring_unfold; reflexivity) with "Harrx")
      as "Harrx".
    iPoseProof (arrayR_charR_anyR _ 5%N
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
    iPoseProof (borrow_arrayR_cstringR _ _
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
    iPoseProof (arrayR_charR_anyR _ 6%N
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
End with_cpp.
