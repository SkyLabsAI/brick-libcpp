(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.all_any_none_of.spec.
Require Import skylabs.brick.libstdcpp.test.all_any_none_of.counting_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.
  Context {MOD : counting_cpp.source ⊧ σ}.

  cpp.spec "counted_all_nonzero(unsigned char)" as counted_all_nonzero_spec
    from counting_cpp.source with
    (\with (k : N)
     \arg{x} "byte" (Vint x)
     \require (k < 3)%N
     \pre _global "all_of_calls" |-> uintR 1$m k
     \post{r : bool}[Vbool r]
       _global "all_of_calls" |-> uintR 1$m (k + 1)%N **
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma counted_all_nonzero_ok :
    verify[counting_cpp.source] counted_all_nonzero_spec.
  Proof using MOD. verify_spec; go. Qed.

  Lemma counted_all_nonzero_predicate_spec (xs : list Z) :
    (lengthZ xs <= 3)%Z ->
    counted_all_nonzero_spec |--
      _global "counted_all_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x => Some (bool_decide (x <> 0)%Z))
          (fun k : Z =>
             _global "all_of_calls" |-> uintR 1$m (Z.to_N k))).
  Proof.
    intros Hlen.
    iApply specify_mono.
    go.
  Qed.

  cpp.spec "counted_any_nonzero(unsigned char)" as counted_any_nonzero_spec
    from counting_cpp.source with
    (\with (k : N)
     \arg{x} "byte" (Vint x)
     \require (k < 3)%N
     \pre _global "any_of_calls" |-> uintR 1$m k
     \post{r : bool}[Vbool r]
       _global "any_of_calls" |-> uintR 1$m (k + 1)%N **
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma counted_any_nonzero_ok :
    verify[counting_cpp.source] counted_any_nonzero_spec.
  Proof using MOD. verify_spec; go. Qed.

  Lemma counted_any_nonzero_predicate_spec (xs : list Z) :
    (lengthZ xs <= 3)%Z ->
    counted_any_nonzero_spec |--
      _global "counted_any_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x => Some (bool_decide (x <> 0)%Z))
          (fun k : Z =>
             _global "any_of_calls" |-> uintR 1$m (Z.to_N k))).
  Proof.
    intros Hlen.
    iApply specify_mono.
    go.
  Qed.

  cpp.spec "counted_none_nonzero(unsigned char)" as counted_none_nonzero_spec
    from counting_cpp.source with
    (\with (k : N)
     \arg{x} "byte" (Vint x)
     \require (k < 3)%N
     \pre _global "none_of_calls" |-> uintR 1$m k
     \post{r : bool}[Vbool r]
       _global "none_of_calls" |-> uintR 1$m (k + 1)%N **
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma counted_none_nonzero_ok :
    verify[counting_cpp.source] counted_none_nonzero_spec.
  Proof using MOD. verify_spec; go. Qed.

  Lemma counted_none_nonzero_predicate_spec (xs : list Z) :
    (lengthZ xs <= 3)%Z ->
    counted_none_nonzero_spec |--
      _global "counted_none_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x => Some (bool_decide (x <> 0)%Z))
          (fun k : Z =>
             _global "none_of_calls" |-> uintR 1$m (Z.to_N k))).
  Proof.
    intros Hlen.
    iApply specify_mono.
    go.
  Qed.

  cpp.spec "all_of_counting_results()" with
    (\pre _global "all_of_calls" |-> anyR Tuint 1$m
     \post _global "all_of_calls" |-> anyR Tuint 1$m).

  Lemma all_of_counting_results_ok :
    verify[counting_cpp.source] "all_of_counting_results()".
  Proof using MOD.
    verify_spec; go.
    iExists (fun x => Some (bool_decide (x <> 0)%Z)),
      (fun k : Z =>
         _global "all_of_calls" |-> uintR 1$m (Z.to_N k)).
    wapply (counted_all_nonzero_predicate_spec [1; 0; 2]).
    { Arith.arith_solve. }
    go.
  Qed.

  cpp.spec "any_of_counting_results()" with
    (\pre _global "any_of_calls" |-> anyR Tuint 1$m
     \post _global "any_of_calls" |-> anyR Tuint 1$m).

  Lemma any_of_counting_results_ok :
    verify[counting_cpp.source] "any_of_counting_results()".
  Proof using MOD.
    verify_spec; go.
    iExists (fun x => Some (bool_decide (x <> 0)%Z)),
      (fun k : Z =>
         _global "any_of_calls" |-> uintR 1$m (Z.to_N k)).
    wapply (counted_any_nonzero_predicate_spec [0; 7; 0]).
    { Arith.arith_solve. }
    go.
  Qed.

  cpp.spec "none_of_counting_results()" with
    (\pre _global "none_of_calls" |-> anyR Tuint 1$m
     \post _global "none_of_calls" |-> anyR Tuint 1$m).

  Lemma none_of_counting_results_ok :
    verify[counting_cpp.source] "none_of_counting_results()".
  Proof using MOD.
    verify_spec; go.
    iExists (fun x => Some (bool_decide (x <> 0)%Z)),
      (fun k : Z =>
         _global "none_of_calls" |-> uintR 1$m (Z.to_N k)).
    wapply (counted_none_nonzero_predicate_spec [0; 7; 0]).
    { Arith.arith_solve. }
    go.
  Qed.

End with_cpp.
