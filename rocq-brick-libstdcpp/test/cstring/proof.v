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

  (* Restored after the byte-array slice landed. This note records why these
     proofs were parked temporarily during focused iteration. *)

  cpp.spec "test_strlen()" default.
  Lemma test_strlen_ok : verify[module] "test_strlen()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcmp()" default.
  Lemma test_strcmp_ok : verify[module] "test_strcmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strncmp()" default.
  Lemma test_strncmp_ok : verify[module] "test_strncmp()".
  Proof. verify_spec; go; ego. Qed.

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
      iPoseProof (object_bytesR_arrayLR_cons s_addr 120%Z
        [120%Z; 99%Z; 100%Z] with "Hs") as "[[#Hty0 H0] Hs]".
      iExists (Vint 120%Z), (cQp.mk false 1%Qp).
      iFrame "H0". iIntros "H0".
      go.
      iEval (rewrite (arrayLR_cons s_addr 1 4 (fun b : Z => ucharR 1$m b)
        120%Z [99%Z; 100%Z])) in "Hs".
      iDestruct "Hs" as "[[#Hty1 H1] Hs]".
      iExists (Vint 120%Z), (cQp.mk false 1%Qp).
      iFrame "H1". iIntros "H1".
      go.
      iEval (rewrite (arrayLR_cons s_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hs".
      iDestruct "Hs" as "[[#Hty2 H2] Hs]".
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "H2". iIntros "H2".
      go.
      iEval (rewrite (arrayLR_cons s_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hs".
      iDestruct "Hs" as "[[#Hty3 H3] Hs]".
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
        go.
        iPoseProof (object_bytesR_arrayLR_cons s_addr 120%Z
          [120%Z; 35%Z; 100%Z] with "Hs") as "[[#Hty0' H0] Hs]".
        iEval (rewrite (arrayLR_cons s_addr 1 4 (fun b : Z => ucharR 1$m b)
          120%Z [35%Z; 100%Z])) in "Hs".
        iDestruct "Hs" as "[[#Hty1' H1] Hs]".
        iEval (rewrite (arrayLR_cons s_addr 2 4 (fun b : Z => ucharR 1$m b)
          35%Z [100%Z])) in "Hs".
        iDestruct "Hs" as "[[#Hty2' H2] Hs]".
        iExists (Vint 35%Z), (cQp.mk false 1%Qp).
        iFrame "H2". iIntros "H2".
        go.
        iEval (rewrite (arrayLR_cons s_addr 3 4 (fun b : Z => ucharR 1$m b)
          100%Z [])) in "Hs".
        iDestruct "Hs" as "[[#Hty3' H3] Hempty2]".
        iExists (Vint 100%Z), (cQp.mk false 1%Qp).
        iFrame "H3". iIntros "H3".
        go.
        iPoseProof (at_zero_elim s_addr with "H0") as "H0".
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

      iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
        [98%Z; 99%Z; 122%Z] with "Hdst") as "[[#Hdst_ty0 Hdst0] Hdst]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty1 Hdst1] Hdst]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty2 Hdst2] Hdst]".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
        122%Z [])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty3 Hdst3] Hdst_empty]".
      iExists (Vint 122%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (object_bytesR_arrayLR_cons src_addr 97%Z
        [98%Z; 99%Z; 100%Z] with "Hsrc") as "[[#Hsrc_ty0 Hsrc0] Hsrc]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc0". iIntros "Hsrc0".
      go.

      iEval (rewrite (arrayLR_cons src_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty1 Hsrc1] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty2 Hsrc2] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty3 Hsrc3] Hsrc_empty2]".
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
        with "Hdst_suffix") as "[Hdst_empty1 Hdst_suffix1]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty1".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 0%N
          [] ltac:(reflexivity) with "Hdst_empty1").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty1]".
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
          with "[$Hdst_empty1 $Hdst_suffix1]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
          [98%Z; 99%Z; 122%Z] with "Hdst_full")
          as "[[#Hdst_ty4 Hdst0] Hdst_arr]".
        iExists (Vint 97%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst0". iIntros "Hdst0".
        go.

        iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
          98%Z [99%Z; 122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty5 Hdst1] Hdst_arr]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full") as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
          99%Z [122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty6 Hdst2] Hdst_arr]".
        iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
          122%Z [])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty7 Hdst3] Hdst_empty2]".
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

      iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
        [98%Z; 99%Z; 100%Z] with "Hdst") as "[[#Hdst_ty0 Hdst0] Hdst_arr]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 100%Z])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty1 Hdst1] Hdst_arr]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty2 Hdst2] Hdst_arr]".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty3 Hdst3] Hdst_empty0]".
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
        with "Hdst_suffix") as "[Hdst_empty1 Hdst_suffix1]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty1".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 0%N
          [] ltac:(reflexivity) with "Hdst_empty1").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty1]".
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
          with "[$Hdst_empty1 $Hdst_suffix1]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
          [98%Z; 99%Z; 100%Z] with "Hdst_full")
          as "[[#Hdst_ty4 Hdst0] Hdst_arr2]".
        iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
          98%Z [99%Z; 100%Z])) in "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[[#Hdst_ty5 Hdst1] Hdst_arr2]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full")
          as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
          99%Z [100%Z])) in "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[[#Hdst_ty6 Hdst2] Hdst_arr3]".
        iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
          100%Z [])) in "Hdst_arr3".
        iDestruct "Hdst_arr3" as "[[#Hdst_ty7 Hdst3] Hdst_empty2]".
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

  cpp.spec "test_memmove_overlap()" default.

  cpp.spec "test_cstring_slice4()" default.
End with_cpp.
