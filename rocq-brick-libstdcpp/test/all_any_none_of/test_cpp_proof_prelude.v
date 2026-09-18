(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.all_any_none_of.spec.
Require Import skylabs.brick.libstdcpp.test.all_any_none_of.test_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  cpp.spec "is_nonzero(unsigned char)" as is_nonzero_spec
    from test_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r]
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma is_nonzero_ok : verify[test_cpp.source] is_nonzero_spec.
  Proof. verify_spec; go. Qed.

  Lemma is_nonzero_predicate_spec (xs : list Z) :
    is_nonzero_spec |--
      _global "is_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x => Some (bool_decide (x <> 0)%Z))
          (fun _ => emp)).
  Proof.
    apply specify_mono; go.
  Qed.

  Definition is_nonzero_predicate_spec_C :=
    [CANCEL] is_nonzero_predicate_spec.
  #[local] Hint Resolve is_nonzero_predicate_spec_C : br_hints.

  cpp.spec "is_seven(unsigned char)" as is_seven_spec
    from test_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r] [| r = bool_decide (x = 7)%Z |]).

  Lemma is_seven_ok : verify[test_cpp.source] is_seven_spec.
  Proof. verify_spec; go. Qed.

  Lemma is_seven_predicate_spec (xs : list Z) :
    is_seven_spec |-- _global "is_seven(unsigned char)" |->
      cptrR (all_any_none_of.predicate_spec xs
        (fun x => Some (bool_decide (x = 7)%Z)) (fun _ => emp)).
  Proof. apply specify_mono; go. Qed.

  Definition is_seven_predicate_spec_C := [CANCEL] is_seven_predicate_spec.
  #[local] Hint Resolve is_seven_predicate_spec_C : br_hints.

  cpp.spec "is_zero(unsigned char)" as is_zero_spec
    from test_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r] [| r = bool_decide (x = 0)%Z |]).

  Lemma is_zero_ok : verify[test_cpp.source] is_zero_spec.
  Proof. verify_spec; go. Qed.

  Lemma is_zero_predicate_spec (xs : list Z) :
    is_zero_spec |-- _global "is_zero(unsigned char)" |->
      cptrR (all_any_none_of.predicate_spec xs
        (fun x => Some (bool_decide (x = 0)%Z)) (fun _ => emp)).
  Proof. apply specify_mono; go. Qed.

  Definition is_zero_predicate_spec_C := [CANCEL] is_zero_predicate_spec.
  #[local] Hint Resolve is_zero_predicate_spec_C : br_hints.

  cpp.spec "has_high_bit(unsigned char)" as has_high_bit_spec
    from test_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r] [| r = bool_decide (128 <= x)%Z |]).

  Lemma has_high_bit_ok : verify[test_cpp.source] has_high_bit_spec.
  Proof.
    verify_spec; go.
    iPureIntro. exact (Z.ge_le_iff x 128).
  Qed.

  Lemma has_high_bit_predicate_spec (xs : list Z) :
    has_high_bit_spec |-- _global "has_high_bit(unsigned char)" |->
      cptrR (all_any_none_of.predicate_spec xs
        (fun x => Some (bool_decide (128 <= x)%Z)) (fun _ => emp)).
  Proof. apply specify_mono; go. Qed.

  Definition has_high_bit_predicate_spec_C := [CANCEL] has_high_bit_predicate_spec.
  #[local] Hint Resolve has_high_bit_predicate_spec_C : br_hints.

  Ltac use_is_nonzero :=
    iExists (fun x => Some (bool_decide (x <> 0)%Z)), (fun _ => emp); go.
  Ltac use_is_seven :=
    iExists (fun x => Some (bool_decide (x = 7)%Z)), (fun _ => emp); go.
  Ltac use_is_zero :=
    iExists (fun x => Some (bool_decide (x = 0)%Z)), (fun _ => emp); go.
  Ltac use_has_high_bit :=
    iExists (fun x => Some (bool_decide (128 <= x)%Z)), (fun _ => emp); go.

End with_cpp.
