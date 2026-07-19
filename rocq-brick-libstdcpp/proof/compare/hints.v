(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.compare.spec.
Require Import skylabs.brick.libstdcpp.compare.inc_compare_cpp.

Import linearity.

(* TODO upstream! *)
#[only(finite)] derive comparison.

(* TODO upstream? *)
#[local] Arguments qual_norm {_} _ !_ /.
#[local] Typeclasses Opaque int_rank.t_leb.
#[local] Typeclasses Opaque int_rank.t_le.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (* TODO upstream? *)
  Section fixed_var_hint.
    Context (tu : translation_unit) (ρ : region).

    Abbreviation interp := (interp tu).
    Abbreviation wp_prval := (wp_prval tu ρ).
    Abbreviation wp_operand := (wp_operand tu ρ).
    Abbreviation wp_lval := (wp_lval tu ρ).
    Abbreviation wp_xval := (wp_xval tu ρ).
    Abbreviation wp_glval := (wp_glval tu ρ).
    Abbreviation wp_init := (wp_init tu ρ).
    Abbreviation wp_initialize := (wp_initialize tu ρ).
    Abbreviation wp_discard := (wp_discard tu ρ).
    Abbreviation wp := (wp tu ρ).
    Abbreviation wp_decl := (wp_decl tu ρ).

    #[local] Open Scope free_scope.

    Lemma wp_lval_global Q nm ty :
      wp.check_global tu nm ty =[Vm]=> true ->
          Q (_global nm) FreeTemps.id
      |-- wp_lval (Eglobal nm ty) Q.
    Proof.
      rewrite RedEq_eq_iff => H.
      apply @wp.wp_lval_global.
      by rewrite RedEq_eq_iff H.
    Qed.
    Definition wp_lval_global_B := [BWD] wp_lval_global.
  End fixed_var_hint.

  #[local] Remove Hints wp.wp_lval_global_B : db_skylabs_wp.
  #[local] Hint Resolve wp_lval_global_B | 150 : db_skylabs_wp.

  Section with_resolve.
    Variables (tu : translation_unit) (ρ : region).

    #[local] Abbreviation wp_init := (wp_init tu ρ).
    #[local] Abbreviation wp_operand := (wp_operand tu ρ).
    #[local] Open Scope free_scope.

    Lemma wp_operand_frame' e :
      ⊢ wp.WPE.Mframe (wp_operand e) (wp_operand e).
    Proof.
      rewrite /wp.WPE.Mframe.
      iIntros "* W".
      by iApply wp_operand_frame.
    Qed.

    Definition strong_ordering_result_names : list PrimString.string :=
      Eval compute in (strong_ordering_result_name <$> enum _).
    Succeed Example foo :
      strong_ordering_result_names = ["equal"; "less"; "greater"]%pstring := eq_refl.

    Definition partial_ordering_result_names : list PrimString.string :=
      Eval compute in (partial_ordering_result_name <$> enum _).
    Succeed Example foo :
      partial_ordering_result_names =
      ["unordered" ; "equivalent" ; "less" ; "greater"]%pstring := eq_refl.

    Definition cmp_expected_cls (te1 : type) : option name :=
      match te1 with
      | Tnum sz sgn =>
        (* from arith_as *)
        if bool_decide (int_rank.t_le int_rank.Iint sz) then
          Some "std::strong_ordering"%cpp_name
        else
          None
      | Tfloat_ fty =>
          Some "std::partial_ordering"%cpp_name
      | _ => None
      end.

    Definition cmp_res (te1 : type) (v1 v2 : val) (p : ptr) (Q : mpred) : mpred :=
      ∃ q,
      match te1, v1, v2 with
      | Tnum sz sgn, Vint a, Vint b =>
        (* from arith_as *)
        if bool_decide (int_rank.t_le int_rank.Iint sz) then
          let cmp_res := Z.compare a b in
          std.compare.strong_ordering_copy_ctor **
          std.compare.strong_ordering_globals q **
          (std.compare.strong_ordering_globals q **
          p |-> std.compare.strong_orderingR 1$m cmp_res -*
          Q)
        else
          False%I
      | Tfloat_ fty, Vfloat f a, Vfloat f' b =>
        match decide (f = fty), decide (f' = fty) with
        | left H, left H' =>
          let a' := eq_rect f float_type.car a fty H in
          let b' := eq_rect f' float_type.car b fty H' in
          let cmp_res := float_value.value_compare a' b' in
          std.compare.partial_ordering_copy_ctor **
          std.compare.partial_ordering_globals q **
          (std.compare.partial_ordering_globals q **
          p |-> std.compare.partial_orderingR 1$m cmp_res -*
          Q)
        | _, _ => False
        end
      | _, _, _ => False
      end.
    #[global] Hint Opaque cmp_res : sl_opacity.
    #[global] Arguments cmp_res !_ /.

    (* Ensure the [wp_init_binop_spaceship] desugaring is valid here.
    The [Econstructor] typechecker is currently trivial, but this will be fixed. *)
    Definition wp_init_binop_spaceship_stdlib_hint_typecheck ty te1 cls :=
      let ctor := cls .:: Nctor [Tref $ Tconst $ Tnamed cls] in
      let res_to_type := fun res_name =>
        let arg := Eglobal (cls .:: Nid res_name) (Tconst (Tnamed cls)) in
        decltype.of_expr (Econstructor ctor [arg] ty) in
      let args : list PrimString.string :=
        match te1 with
        | Tnum _ _ => strong_ordering_result_names
        | Tfloat_ _ => partial_ordering_result_names
        | _ => []
        end in
      bool_decide (res_to_type <$> args = const (Some ty) <$> args).

    Lemma wp_init_binop_spaceship_stdlib_hint e1 e2 ty te1 (addr : ptr) cls Q :
      (drop_qualifiers (type_of e1), drop_qualifiers (type_of e2), snd (decompose_type ty)) =[Vm]=> (te1, te1, Tnamed cls) ->
      (Tnamed <$> cmp_expected_cls te1) =[Vm]=> Some ty ->
      wp_init_binop_spaceship_stdlib_hint_typecheck ty te1 cls =[Vm]=> true ->
      (letI* '(v1, v2), free := eval2 (evaluation_order.order_of (language_version tu) OOSpaceship)
        (wp_operand e1) (wp_operand e2) in
      cmp_res te1 v1 v2 addr
        (* XXX [(1 >*> 1) >*>] is unfortunate temporary noise *)
        (Q ((1 >*> 1) >*> free)))
    |-- wp_init ty addr (Ebinop Bcmp e1 e2 ty) Q.
    Proof.
      rewrite /cmp_expected_cls !RedEq_eq_iff; intros ?? Htype.
      clear Htype. (* actual typechecking's trivial. *)
      rewrite -wp_init_binop_spaceship /=; last congruence.
      destruct (decompose_type ty) eqn:?; simplify_eq/=.
      iApply (nd_seq_frame with "[][] []"); [iApply wp_operand_frame'..|].
      iIntros ([v1 v2] ?) "[% W]".
      destruct cmp_res_name eqn:C;
        rewrite /cmp_res /cmp_res_name in C |- *.
      2: repeat (case_match; simplify_eq/=; try iDestruct "W" as "[]").
      iDestruct "W" as "?"; work.

      repeat (case_match; try by exfalso); simplify_eq/=.
      all: go.
      (* ^^ applies invoke.wp_init_ctor_C *)
      all: rewrite -E.wp_lval_global /= /read_decl /=.
      all: rewrite /strong_ordering_result_name /partial_ordering_result_name.
      all: (iSplitR; first by (repeat case_match; work)).
      all: work.
      all: iExists q; [> iExists (z ?= z0) | iExists (float_value.value_compare c c0) ].
      all: repeat case_match.
      all: work.
    Qed.
    Definition wp_init_binop_spaceship_stdlib_hint_B :=
      [BWD] wp_init_binop_spaceship_stdlib_hint.

  End with_resolve.
End with_cpp.

#[export] Hint Resolve wp_init_binop_spaceship_stdlib_hint_B | 150 : db_skylabs_wp.

