(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.brick.libstdcpp.optional.model.

Module optional_uint8.
  (**
     The object spine hides the implementation-dependent layout while
     recording whether a contained-value address exists.
   *)
  Parameter spineR :
    forall `{Σ : cpp_logic} {σ : genv}, cQp.t -> option ptr -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,
         type_ptr="std::optional<unsigned char>")] derive spineR.

  #[global] Declare Instance spineR_agree
      `{Σ : cpp_logic} {σ : genv} q contained q' contained' :
    Observe2 [| contained = contained' |]
      (spineR q contained) (spineR q' contained').
  (**
     Const qualification shifts the opaque spine and, when engaged, the
     contained byte cell recorded by the spine.
   *)
  Parameter spineR_wp_const :
    forall `{Σ : cpp_logic} {σ : genv}
      (tu : translation_unit) (from to : cQp.t) (p : ptr)
      (contained : option ptr) (Q : mpred),
    p |-> spineR from contained ⊢
      (p |-> spineR to contained -∗
       match contained with
       | None => Q
       | Some contained => wp_const tu from to contained Tuchar Q
       end) -∗
      wp_const tu from to p "std::optional<unsigned char>" Q.

  #[global] Instance spineR_wp_const_C
      `{Σ : cpp_logic} {σ : genv}
      (tu : translation_unit) (from to : cQp.t) (p : ptr)
      (contained : option ptr) (Q : mpred) :
    CancelX MatchNormal
      [p |-> spineR from contained] [tele] CoverAny
      [wp_const tu from to p "std::optional<unsigned char>" Q] :=
    Build_CancelX'
      [p |-> spineR from contained]
      [wp_const tu from to p "std::optional<unsigned char>" Q]
      [tele] [] D.mtO
      [(p |-> spineR to contained -∗
        match contained with
        | None => Q
        | Some contained => wp_const tu from to contained Tuchar Q
        end)%I]
      (orient.from_reif [tele] syntactic_bi.EmpT D.mtO
        (syntactic_bi.WandT
          (syntactic_bi.InjT (p |-> spineR to contained))
          (syntactic_bi.InjT
            (match contained with
             | None => Q
             | Some contained => wp_const tu from to contained Tuchar Q
             end)))
        (orient.no_P' [tele]
          (p |-> spineR to contained -∗
           match contained with
           | None => Q
           | Some contained => wp_const tu from to contained Tuchar Q
           end)%I
          (spineR_wp_const tu from to p contained Q))).


  (**
     [R q st contained] owns one optional object.  An engaged object also
     owns the exact byte cell returned by const-lvalue dereference.
   *)
  sl.lock
  Definition R `{Σ : cpp_logic} {σ : genv}
      (q : cQp.t) (st : optional_uint8_model.state)
      (contained : option ptr) : Rep :=
    spineR q contained **
    match st, contained with
    | None, None => emp
    | Some b, Some p => pureR (p |-> ucharR q b)
    | _, _ => [| False |]
    end.

  #[only(lazy_unfold(global))] derive R.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr)] derive R.
  (** The whole optional representation follows the spine and byte shifts. *)
  Lemma R_wp_const
      `{Σ : cpp_logic} {σ : genv}
      (tu : translation_unit) (from to : cQp.t) (p : ptr)
      (st : optional_uint8_model.state) (contained : option ptr) (Q : mpred) :
    p |-> R from st contained ⊢
      (p |-> R to st contained -∗ Q) -∗
        wp_const tu from to p "std::optional<unsigned char>" Q.
  Proof.
    rewrite !R.unlock.
    destruct st as [b|], contained as [contained|]; simpl.
    - rewrite !_at_sep !_at_pureR.
      iIntros "[Hspine Hbyte] Hcont".
      iApply (spineR_wp_const with "Hspine").
      iIntros "Hspine".
      iApply (const.wp_const_num with "Hbyte").
      iIntros "Hbyte".
      iApply "Hcont".
      iFrame.
    - rewrite !_at_sep !_at_only_provable.
      iIntros "[_ %]".
      done.
    - rewrite !_at_sep !_at_only_provable.
      iIntros "[_ %]".
      done.
    - rewrite !_at_sep !_at_emp.
      iIntros "[Hspine _] Hcont".
      iApply (spineR_wp_const with "Hspine").
      iIntros "Hspine".
      iApply "Hcont".
      iFrame.
  Qed.

  #[global] Instance R_wp_const_C
      `{Σ : cpp_logic} {σ : genv}
      (tu : translation_unit) (from to : cQp.t) (p : ptr)
      (st : optional_uint8_model.state) (contained : option ptr) (Q : mpred) :
    CancelX MatchNormal
      [p |-> R from st contained] [tele] CoverAny
      [wp_const tu from to p "std::optional<unsigned char>" Q] :=
    Build_CancelX'
      [p |-> R from st contained]
      [wp_const tu from to p "std::optional<unsigned char>" Q]
      [tele] [] D.mtO
      [(p |-> R to st contained -∗ Q)%I]
      (orient.from_reif [tele] syntactic_bi.EmpT D.mtO
        (syntactic_bi.WandT
          (syntactic_bi.InjT (p |-> R to st contained))
          (syntactic_bi.InjT Q))
        (orient.no_P' [tele]
          (p |-> R to st contained -∗ Q)%I
          (R_wp_const tu from to p st contained Q))).


  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.
    #[global] Instance R_learn : LearnEqF2 R :=
      ltac:(solve_learnable).
  End with_cpp.
End optional_uint8.
