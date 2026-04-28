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

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_strlen_embedded_null()" default.
  Lemma test_strlen_embedded_null_ok :
    verify[module] "test_strlen_embedded_null()".
  Admitted.

  cpp.spec "test_strcmp_embedded_null()" default.
  Lemma test_strcmp_embedded_null_ok :
    verify[module] "test_strcmp_embedded_null()".
  Admitted.

  cpp.spec "test_strncmp_embedded_null()" default.
  Lemma test_strncmp_embedded_null_ok :
    verify[module] "test_strncmp_embedded_null()".
  Admitted.

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
    iPoseProof (arrayLR_charR_arrayLR_anyR _ 1$m
      (cstring.to_zstring "ab"%bs ++ [98%N; 99%N; 0%N]) with "Harr")
      as "Harr".
    go.
    iFrame "Harr".
    go.
  Qed.

  cpp.spec "test_memset_embedded_null()" default.
  Lemma test_memset_embedded_null_ok :
    verify[module] "test_memset_embedded_null()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (s_addr |-> arrayLR "unsigned char" (1 + 1) 4
      (fun v : Z => ucharR 1$m v) [99%Z; 100%Z]) as "Htail".
    iDestruct select (s_addr .["unsigned char" ! 1] |-> ucharR 1$m 98%Z)
      as "H1".
    iDestruct select (s_addr .["unsigned char" ! 0] |-> ucharR 1$m 97%Z)
      as "H0".
    iEval (rewrite (arrayLR_cons s_addr 2 4 (fun b : Z => ucharR 1$m b)
      99%Z [100%Z])) in "Htail".
    iDestruct "Htail" as "[[#Hty2 H2] Htail]".
    iPoseProof (at_uchar_offset_add_intro s_addr 1 1 2
      (ucharR 1$m 99%Z) ltac:(lia) with "H2") as "H2".
    iPoseProof (uchar_cells_object_bytesR_two (s_addr .[Tuchar ! 1])
      98%Z 99%Z with "[$H1 $H2]") as "Htarget".
    iEval (rewrite (arrayLR_cons s_addr 3 4 (fun b : Z => ucharR 1$m b)
      100%Z [])) in "Htail".
    iDestruct "Htail" as "[[#Hty3 H3] Hempty]".
    iExists Tuchar.
    iSplitL "Htarget".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 1$m 2%N
        [98%Z; 99%Z] ltac:(reflexivity) with "Htarget").
    - iIntros "Htarget".
      go.
      iPoseProof (object_bytesR_arrayLR_cons (s_addr .[Tuchar ! 1]) 0%Z
        [0%Z] with "Htarget") as "[[#Hty1 H1] Htarget]".
      iEval (rewrite (arrayLR_cons (s_addr .[Tuchar ! 1]) 1 2
        (fun b : Z => ucharR 1$m b) 0%Z [])) in "Htarget".
      iDestruct "Htarget" as "[[#Hty2' H2] Hempty2]".
      iFrame "H0". iIntros "H0".
      go.
      iPoseProof (at_zero_elim (s_addr .[Tuchar ! 1]) with "H1") as "H1".
      iFrame "H1". iIntros "H1".
      go.
      iPoseProof (at_uchar_offset_add_elim s_addr 1 1 2
        (ucharR 1$m 0%Z) ltac:(lia) with "H2") as "H2".
      iFrame "H2". iIntros "H2".
      go.
      iFrame "H3". iIntros "H3".
      go.
      iPoseProof (at_zero_elim s_addr with "H0") as "H0".
      iPoseProof (uchar_cells_object_bytesR_two s_addr 97%Z 0%Z
        with "[$H0 $H1]") as "Hhead".
      iPoseProof (at_uchar_offset_add_intro s_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "H3") as "H3".
      iPoseProof (uchar_cells_object_bytesR_two (s_addr .[Tuchar ! 2])
        0%Z 100%Z with "[$H2 $H3]") as "Htail".
      iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 0%Z] [0%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hhead $Htail]") as "Hs".
      iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
        [97%Z; 0%Z; 0%Z; 100%Z] ltac:(reflexivity) with "Hs") as "Hs".
      iFrame "Hs".
      go.
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
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
      [97%Z; 0%Z; 98%Z; 0%Z]
      ltac:(reflexivity) with "Hs") as "Hs".
    iFrame "Hs".
    go.
    rewrite o_sub_sub in H.
    simpl in H.
    contradiction.
  Qed.

  cpp.spec "test_memcmp_embedded_null()" default.

  cpp.spec "test_memcpy_embedded_null()" default.

  cpp.spec "test_memmove_embedded_null()" default.

End with_cpp.
