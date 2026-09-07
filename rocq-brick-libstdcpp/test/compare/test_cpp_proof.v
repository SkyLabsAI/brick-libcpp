(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.test.

Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.compare.spec.
Require Import skylabs.brick.libstdcpp.compare.hints.
Require Import skylabs.brick.libstdcpp.test.compare.test_cpp.

Require Import skylabs.brick.libstdcpp.test.compare.int_point.
Require Import skylabs.brick.libstdcpp.test.compare.weak_bucket.
Require Import skylabs.brick.libstdcpp.test.compare.floating_box.
Require Import skylabs.brick.libstdcpp.test.compare.test_specs.

Import linearity.

(* Test Warnings. *)
#[local] Set Warnings "+sl-transparent-constants".
(* Test Warnings. *)

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  (*
  Lemma valid_quot (z d : Z) :
    0 < d ->
    valid<"int"> (Vint z) ->
    (* valid<"int"> (Vint (z `quot` d)). *)
    bitsize.bound bitsize.W32 Signed (z `quot` d).
  Proof.
    intros.

    type.has_type_prop_prep.
    arith_simpl.
    destruct (decide (0 <= z)).
    {
      suff: 0 <= z `quot` d < 2147483648 by lia.
      apply Z.quot_range_nonneg; lia.
    }
    suff: 0 <= -z `quot` d < 2147483649 by lia.
    rewrite -Z.quot_opp_l; last lia.
    apply Z.quot_range_nonneg; lia.
  Qed.
  *)

  (* Hint Resolve valid_quot : pure. *)

  Lemma valid_quot' (z d : Z) :
    0 <> d ->
    valid<"int"> (Vint (z * Z.sgn d)) ->
    (* valid<"int"> (Vint (z `quot` d)). *)
    bitsize.bound bitsize.W32 Signed (z `quot` d).
  Proof.
    intros Hd Hz.
    wlog: d Hd z Hz / 0 < d => [|{}Hd]. {
      destruct (decide (0 < d)); first exact.

      (* Search (- - ?x = ?x)%Z. *)
      rewrite -(Z.opp_involutive d) Z.quot_opp_r -?Z.quot_opp_l; [|lia..].
      apply; try lia.
      move: Hz.
      rewrite (Z.sgn_neg d) ?(Z.sgn_pos (-d)); arith_solve.
    }
    (* apply valid_quot; arith_solve. *)
    intros.

    type.has_type_prop_prep.
    rewrite Z.sgn_pos in Hz; last lia.
    arith_simpl.
    destruct (decide (0 <= z)).
    {
      suff: 0 <= z `quot` d < 2147483648 by lia.
      apply Z.quot_range_nonneg; lia.
    }
    suff: 0 <= -z `quot` d < 2147483649 by lia.
    rewrite -Z.quot_opp_l; last lia.
    apply Z.quot_range_nonneg; lia.
  Qed.
  #[local] Hint Resolve valid_quot' : pure.

  Section proofs.
    Lemma int_point_dtor_ok :
      verify[ source ] int_point_dtor.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition int_point_dtor_B := [LINK] int_point_dtor_ok.
    #[local] Hint Resolve int_point_dtor_B : sl_opacity.

    Lemma int_point_eq_ok :
      verify[ source ] int_point_eq.
    Proof using MOD.
      verify_spec.
      go.
      (* destruct m, m'. *)
      vc_split; go; iPureIntro.
      { destruct m, m'. naive_solver. }
      { case_bool_decide; naive_solver. }
    Qed.
    Definition int_point_eq_B := [LINK] int_point_eq_ok.
    #[local] Hint Resolve int_point_eq_B : sl_opacity.

    Lemma int_point_spaceship_ok :
      verify[ source ] int_point_spaceship.
    Proof using MOD.
      verify_spec.
      go.
      destruct (Z.compare (int_point_x _)) eqn:Hx; go.
      1: destruct (Z.compare (int_point_y _)) eqn:Hy; go.
      all: by rewrite /int_point_compare Hx ?Hy /=.
    Qed.
    Definition int_point_spaceship_B := [LINK] int_point_spaceship_ok.
    #[local] Hint Resolve int_point_spaceship_B : sl_opacity.

    Lemma weak_bucket_dtor_ok :
      verify[ source ] weak_bucket_dtor.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition weak_bucket_dtor_B := [LINK] weak_bucket_dtor_ok.
    #[local] Hint Resolve weak_bucket_dtor_B : sl_opacity.

    Lemma weak_bucket_eq_ok :
      verify[ source ] weak_bucket_eq.
    Proof using MOD. verify_spec; go. Qed.

    Definition weak_bucket_eq_B := [LINK] weak_bucket_eq_ok.
    #[local] Hint Resolve weak_bucket_eq_B : sl_opacity.

    Lemma weak_bucket_spaceship_ok :
      verify[ source ] weak_bucket_spaceship.
    Proof using MOD.
      verify_spec.
      go.
      wp_if; go.
      wp_if; go.
      all: progress rewrite /weak_bucket_compare/weak_bucket_bucket/=.
      { by rewrite Zaux.Zcompare_Gt. }
      { by rewrite Zaux.Zcompare_Eq. }
    Qed.
    Definition weak_bucket_spaceship_B := [LINK] weak_bucket_spaceship_ok.
    #[local] Hint Resolve weak_bucket_spaceship_B : sl_opacity.

    Lemma floating_box_dtor_ok :
      verify[ source ] floating_box_dtor.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition floating_box_dtor_B := [LINK] floating_box_dtor_ok.
    #[local] Hint Resolve floating_box_dtor_B : sl_opacity.

    Lemma floating_box_eq_ok :
      verify[ source ] floating_box_eq.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition floating_box_eq_B := [LINK] floating_box_eq_ok.
    #[local] Hint Resolve floating_box_eq_B : sl_opacity.

    Lemma floating_box_spaceship_ok :
      verify[ source ] floating_box_spaceship.
    Proof using MOD.
      verify_spec; go.
      destruct float_value.value_compare as [[]|] eqn:Hx; go.
    Qed.
    Definition floating_box_spaceship_B := [LINK] floating_box_spaceship_ok.
    #[local] Hint Resolve floating_box_spaceship_B : sl_opacity.

    Lemma test_integral_spaceship_ok :
      verify[ source ] test_integral_spaceship.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_integral_spaceship_B := [LINK] test_integral_spaceship_ok.
    #[local] Hint Resolve test_integral_spaceship_B : sl_opacity.

    Lemma test_floating_spaceship_ok :
      verify[ source ] test_floating_spaceship.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_floating_spaceship_B := [LINK] test_floating_spaceship_ok.
    #[local] Hint Resolve test_floating_spaceship_B : sl_opacity.

    Lemma test_comparison_categories_ok :
      verify[ source ] test_comparison_categories.
    Proof using MOD.
      verify_spec.
      Time go.
    Qed.
    Definition test_comparison_categories_B := [LINK] test_comparison_categories_ok.
    #[local] Hint Resolve test_comparison_categories_B : sl_opacity.

    Lemma test_defaulted_integer_class_ok :
      verify?[ source ] test_defaulted_integer_class.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_defaulted_integer_class_B := [LINK] test_defaulted_integer_class_ok.
    #[local] Hint Resolve test_defaulted_integer_class_B : sl_opacity.

    Lemma test_weak_ordering_class_ok :
      verify[ source ] test_weak_ordering_class.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_weak_ordering_class_B := [LINK] test_weak_ordering_class_ok.
    #[local] Hint Resolve test_weak_ordering_class_B : sl_opacity.

    Lemma test_defaulted_floating_class_ok :
      verify[ source ] test_defaulted_floating_class.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition test_defaulted_floating_class_B := [LINK] test_defaulted_floating_class_ok.
    #[local] Hint Resolve test_defaulted_floating_class_B : sl_opacity.

    Lemma main_ok :
      verify[ source ] main.
    Proof using MOD.
      verify_spec.
      go.
    Qed.
    Definition main_B := [LINK] main_ok.
    #[local] Hint Resolve main_B : sl_opacity.

    Lemma specs_ok :
      denoteModule source **
      ▷ test_quiet_NaN **
      ▷ (std.cassert.specs
      ** std.compare.specs)
      |-- main.
    Proof using MOD.
      rewrite /std.cassert.specs /std.compare.specs.
      work.
    Qed.
  End proofs.
End with_cpp.
