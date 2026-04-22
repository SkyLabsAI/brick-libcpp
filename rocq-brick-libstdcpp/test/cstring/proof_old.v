(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Import skylabs.brick.libstdcpp.cstring.pred_old.
Require Import skylabs.brick.libstdcpp.test.cstring.test_cpp.

#[local] Definition embedded_null_lit (c : N) : literal_string.t :=
  literal_string.of_list_N [97%N; 98%N; 0%N; c].

#[local] Lemma embedded_null_lit_to_list c :
  (c < 2 ^ 8)%N ->
  literal_string.to_list_N (embedded_null_lit c) = [97%N; 98%N; 0%N; c].
Proof.
  intros Hc.
  rewrite /embedded_null_lit literal_string.to_of_list_N.
  reflexivity.
  assert (Hbpc :
    (literal_string.bpc_of_list_N [97%N; 98%N; 0%N; c] <= 263)%N).
  { unfold literal_string.bpc_of_list_N; cbn.
    apply (N.Div0.div_le_upper_bound _ _ 263%N).
    eapply N.le_trans.
    - apply N.add_le_mono_r. apply N.log2_up_le_lin. lia.
    - lia. }
  cbn. lia.
Qed.

#[local] Lemma embedded_null_prefix_WF `{σ : genv} :
  cstring.WF "ab"%bs.
Proof.
  apply cstring.WF_cons; [change (Byte.x61 <> Byte.x00); congruence|].
  apply cstring.WF_cons; [change (Byte.x62 <> Byte.x00); congruence|].
  apply cstring.WF_nil.
Qed.

#[local] Lemma existing_embedded_null_lit_bytes :
  literal_string.to_list_N cstringz.ab_0_cd_lit ++ [0%N] =
  cstring.to_zstring "ab"%bs ++ [99%N; 100%N; 0%N].
Proof.
  rewrite cstring.to_zstring_unfold. vm_compute. reflexivity.
Qed.

#[local] Lemma existing_embedded_null_lit_range :
  List.Forall (fun x => (x < 2 ^ 8)%N)
    (cstring.to_zstring "ab"%bs ++ [99%N; 100%N; 0%N]).
Proof.
  rewrite cstring.to_zstring_unfold.
  do 6 (constructor; [reflexivity|]); constructor.
Qed.

#[local] Lemma embedded_null_lit_bytes c :
  (c < 2 ^ 8)%N ->
  literal_string.to_list_N (embedded_null_lit c) ++ [0%N] =
  cstring.to_zstring "ab"%bs ++ [c; 0%N].
Proof.
  intros Hc.
  rewrite cstring.to_zstring_unfold.
  rewrite embedded_null_lit_to_list; [reflexivity|exact Hc].
Qed.

#[local] Lemma embedded_null_lit_range c :
  (c < 2 ^ 8)%N ->
  List.Forall (fun x => (x < 2 ^ 8)%N)
    (cstring.to_zstring "ab"%bs ++ [c; 0%N]).
Proof.
  intros Hc.
  rewrite cstring.to_zstring_unfold.
  repeat constructor; try assumption;
    change (97 < 256)%N || change (98 < 256)%N || change (0 < 256)%N;
    reflexivity.
Qed.

#[local] Lemma borrow_cstringz_cstringR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q s tail :
  cstring.WF s ->
  p |-> cstringz.R q s tail ⊢
  p |-> cstring.R q s ∗
  (p |-> cstring.R q s -∗ p |-> cstringz.R q s tail).
Proof.
  intros Hwf.
  rewrite /cstringz.R.
  rewrite (arrayR_app (fun c : N => charR q c) (Tchar_ char_type.Cchar)).
  iIntros "[Hs Htail]".
  iSplitL "Hs".
  - iApply cstringz.at_R_cstringR.
    { exact Hwf. }
    rewrite /cstringz.R app_nil_r.
    iFrame.
  - iIntros "Hs".
    iPoseProof (cstringz.at_cstringR_R with "Hs") as "Hs".
    rewrite /cstringz.R app_nil_r.
    iFrame.
Qed.

#[local] Lemma at_string_bytesR_cstringz_R `{Σ : cpp_logic, σ : genv}
    (p : ptr) q lit s tail :
  literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
  List.Forall (fun x => (x < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
  p |-> string_bytesR char_type.Cchar q lit ⊢
  p |-> cstringz.R q s tail.
Proof.
  intros Hbytes Hrange.
  iIntros "Hlit".
  iApply (cstringz.at_string_bytesR_R with "Hlit").
  - exact Hbytes.
  - exact Hrange.
Qed.

#[local] Lemma at_cstringz_R_string_bytesR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q lit s tail :
  literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
  List.Forall (fun x => (x < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
  p |-> cstringz.R q s tail ⊢
  p |-> string_bytesR char_type.Cchar q lit.
Proof.
  intros Hbytes Hrange.
  iIntros "HR".
  iApply (cstringz.at_R_string_bytesR with "HR").
  - exact Hbytes.
  - exact Hrange.
Qed.

#[local] Lemma borrow_literal_cstringR `{Σ : cpp_logic, σ : genv}
    (p : ptr) q lit s tail :
  cstring.WF s ->
  literal_string.to_list_N lit ++ [0%N] = cstring.to_zstring s ++ tail ->
  List.Forall (fun x => (x < 2 ^ 8)%N) (cstring.to_zstring s ++ tail) ->
  p |-> string_bytesR char_type.Cchar q lit ⊢
  p |-> cstring.R q s ∗
  (p |-> cstring.R q s -∗
   p |-> string_bytesR char_type.Cchar q lit).
Proof.
  intros Hwf Hbytes Hrange.
  iIntros "Hlit".
  iPoseProof (at_string_bytesR_cstringz_R with "Hlit") as "HR".
  { exact Hbytes. }
  { exact Hrange. }
  iPoseProof (borrow_cstringz_cstringR with "HR") as "[Hab Hclose]".
  { exact Hwf. }
  iFrame "Hab".
  iIntros "Hab".
  iPoseProof ("Hclose" with "Hab") as "HR".
  iApply (at_cstringz_R_string_bytesR with "HR").
  - exact Hbytes.
  - exact Hrange.
Qed.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_strlen()" default.
  Lemma test_strlen_ok : verify[module] "test_strlen()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strlen_embedded_null()" default.
  Lemma test_strlen_embedded_null_ok :
    verify[module] "test_strlen_embedded_null()".
  Proof.
    verify_spec; go.
    iPoseProof (borrow_literal_cstringR _ _ cstringz.ab_0_cd_lit "ab"%bs
      [99%N; 100%N; 0%N] embedded_null_prefix_WF
      existing_embedded_null_lit_bytes existing_embedded_null_lit_range
      with "[$]")
      as "[Hab Hclose]".
    iExists _, "ab"%bs. iFrame "Hab".
    iSplit; [go|].
    iIntros "Hab".
    iPoseProof ("Hclose" with "Hab") as "Hlit".
    go.
  Qed.

  cpp.spec "test_strcmp()" default.
  Lemma test_strcmp_ok : verify[module] "test_strcmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcmp_embedded_null()" default.
  Lemma test_strcmp_embedded_null_ok :
    verify[module] "test_strcmp_embedded_null()".
  Proof.
    verify_spec; go.
    pose proof (embedded_null_lit_bytes 120%N
      ltac:(change (120 < 256)%N; reflexivity)) as Hxbytes.
    pose proof (embedded_null_lit_range 120%N
      ltac:(change (120 < 256)%N; reflexivity)) as Hxrange.
    pose proof (embedded_null_lit_bytes 121%N
      ltac:(change (121 < 256)%N; reflexivity)) as Hybytes.
    pose proof (embedded_null_lit_range 121%N
      ltac:(change (121 < 256)%N; reflexivity)) as Hyrange.
    iPoseProof (borrow_literal_cstringR _ _ (embedded_null_lit 120%N) "ab"%bs
      [120%N; 0%N] embedded_null_prefix_WF Hxbytes Hxrange with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_literal_cstringR _ _ (embedded_null_lit 121%N) "ab"%bs
      [121%N; 0%N] embedded_null_prefix_WF Hybytes Hyrange with "[$]")
      as "[Hy Hclosey]".
    iExists _, "ab"%bs, _, "ab"%bs. iFrame "Hx Hy".
    iIntros "[Hx Hy]".
    iPoseProof ("Hclosex" with "Hx") as "Hlitx".
    iPoseProof ("Hclosey" with "Hy") as "Hlity".
    go.
  Qed.

  cpp.spec "test_strncmp()" default.
  Lemma test_strncmp_ok : verify[module] "test_strncmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strncmp_embedded_null()" default.
  Lemma test_strncmp_embedded_null_ok :
    verify[module] "test_strncmp_embedded_null()".
  Proof.
    verify_spec; go.
    pose proof (embedded_null_lit_bytes 120%N
      ltac:(change (120 < 256)%N; reflexivity)) as Hxbytes.
    pose proof (embedded_null_lit_range 120%N
      ltac:(change (120 < 256)%N; reflexivity)) as Hxrange.
    pose proof (embedded_null_lit_bytes 121%N
      ltac:(change (121 < 256)%N; reflexivity)) as Hybytes.
    pose proof (embedded_null_lit_range 121%N
      ltac:(change (121 < 256)%N; reflexivity)) as Hyrange.
    iPoseProof (borrow_literal_cstringR _ _ (embedded_null_lit 120%N) "ab"%bs
      [120%N; 0%N] embedded_null_prefix_WF Hxbytes Hxrange with "[$]")
      as "[Hx Hclosex]".
    iPoseProof (borrow_literal_cstringR _ _ (embedded_null_lit 121%N) "ab"%bs
      [121%N; 0%N] embedded_null_prefix_WF Hybytes Hyrange with "[$]")
      as "[Hy Hclosey]".
    iExists _, "ab"%bs, _, "ab"%bs. iFrame "Hx Hy".
    iIntros "[Hx Hy]".
    iPoseProof ("Hclosex" with "Hx") as "Hlitx".
    iPoseProof ("Hclosey" with "Hy") as "Hlity".
    go.
  Qed.

  cpp.spec "test_cstring_slice1()" default.
  Lemma test_cstring_slice1_ok : verify[module] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.
End with_cpp.
