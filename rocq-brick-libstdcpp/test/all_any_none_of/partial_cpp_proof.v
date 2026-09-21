(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.all_any_none_of.spec.
Require Import skylabs.brick.libstdcpp.test.all_any_none_of.partial_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  cpp.spec "partial_is_nonzero(unsigned char)" as partial_is_nonzero_spec
    from partial_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r]
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma partial_is_nonzero_ok :
    verify[partial_cpp.source] partial_is_nonzero_spec.
  Proof. verify_spec; go. Qed.

  Lemma partial_is_nonzero_predicate_spec (xs : list Z) :
    partial_is_nonzero_spec |--
      _global "partial_is_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x =>
             if bool_decide (x = 0)%Z then Some false else None)
          (fun _ => emp)).
  Proof.
    apply specify_mono.
    go.
    case_bool_decide; go.
    subst x.
    iPureIntro; lia.
  Qed.

  Definition partial_is_nonzero_predicate_spec_C :=
    [CANCEL] partial_is_nonzero_predicate_spec.
  #[local] Hint Resolve partial_is_nonzero_predicate_spec_C : br_hints.

  Context {MOD : partial_cpp.source ⊧ σ}.

  cpp.spec "all_of_uses_partial_predicate()" default.
  Lemma all_of_uses_partial_predicate_ok :
    verify[partial_cpp.source] "all_of_uses_partial_predicate()".
  Proof using MOD.
    verify_spec; go.
    iExists (fun x =>
      if bool_decide (x = 0)%Z then Some false else None),
      (fun _ => emp).
    go.
  Qed.

End with_cpp.
