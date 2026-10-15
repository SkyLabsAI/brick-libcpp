(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.test.vector.alias_cpp.
Require Import skylabs.auto.cpp.prelude.test.

(** Rejected claims about the copied value and index.
    The final goals in [alias_cpp_proof.expected] pin the rejected claims to
    [7 = 8] and [4 = 9], rather than an unrelated verification failure.
    Positive clients are verified in [test_cpp_proof.v]. *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : alias_cpp.source ⊧ σ}.
  Import linearity.
  Import normalize.normalize_ptr normalize.only_provable_norm.
  #[local] Hint Resolve prim.primR_aggressiveC : sl_opacity.

  cpp.spec "AliasAppend(std::vector<int, std::allocator<int>>&)" as append_wrong_value with
    (\arg{vp} "v" (Vptr vp)
     \with st
     \pre vp |-> std.vector.R_cap "int" 1$m 1 st [7]
     \post vp |-> std.vector.R_resized "int" 1$m 2 st [7; 8]).
  Goal verify[ source ] append_wrong_value.
  Proof using MOD.
    verify_spec. go.
    Fail solve [iExists (Some 0%Z), (8%Z), (cQp.m 1); go].
    iExists (Some 0%Z), (7%Z), (cQp.m 1). go.
    Show. Fail Qed.
  Abort.

  cpp.spec "AliasAppend(std::vector<int, std::allocator<int>>&)" as append_wrong_index with
    (\arg{vp} "v" (Vptr vp)
     \with st
     \pre vp |-> std.vector.R_cap "int" 1$m 2 st [7; 8]
     \post vp |-> std.vector.R_resized "int" 1$m 3 st [7; 8; 8]).
  Goal verify[ source ] append_wrong_index.
  Proof using MOD.
    verify_spec. go.
    Fail solve [iExists (Some 1%Z), (8%Z), (cQp.m 1); go].
    iExists (Some 0%Z), (7%Z), (cQp.m 1). go.
    Show. Fail Qed.
  Abort.

  cpp.spec "AliasFill(std::vector<int, std::allocator<int>>&, unsigned long)" as fill_wrong_value with
    (\arg{vp} "v" (Vptr vp)
     \arg "n" (Vint 4)
     \with st
     \pre vp |-> std.vector.R_cap "int" 1$m 2 st [9; 4]
     \post vp |-> std.vector.R_resized "int" 1$m 4 st [9; 4; 9; 9]).
  Goal verify[ source ] fill_wrong_value.
  Proof using MOD.
    verify_spec. go.
    Fail solve [iExists (Some 1%Z), (9%Z), (cQp.m 1); go].
    iExists (Some 1%Z), (4%Z), (cQp.m 1). go.
    Show. Fail Qed.
  Abort.
End with_cpp.
