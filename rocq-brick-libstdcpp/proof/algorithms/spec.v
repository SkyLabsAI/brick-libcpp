(**
 * Copyright (C) 2025 SkyLabs AI, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.

Require Import skylabs.prelude.under_rel_proper.

Require Import skylabs.cpp.spec.concepts.

Require Export skylabs.brick.libstdcpp.algorithms.inc_algorithms_cpp.
Require Export skylabs.brick.libstdcpp.algorithms.inc_algorithms_cpp_templates.
Require Export skylabs.brick.libstdcpp.iterator.spec.

Section lists.

  Fixpoint list_findZ_from {A} (P : A → Prop) `{!∀ x : A, Decision (P x)} (base : Z) (xs : list A) : option (Z * A) :=
    match xs with
    | [] => None
    | x :: xs =>
        if bool_decide (P x) then
          Some (base, x)
        else
          list_findZ_from P (base + 1) xs
    end.
  #[global] Arguments list_findZ_from _ _ _ _ !xs /.

  Lemma list_findZ_to_nat {A} (P : A → Prop) `{!∀ x : A, Decision (P x)} base xs :
    list_findZ_from P base xs = prod_map (fun i => base + Z.of_nat i)%Z id <$> list_find P xs.
  Proof.
    elim: xs base => [|x xs IH] base //=.
    rewrite bool_decide_decide.
    case: decide => [HP|HnP] /=.
    - do 2 f_equal; lia.
    - rewrite -option_fmap_compose /compose IH.
      case: list_find => [[i a]/=|//].
      do 2 f_equal; lia.
  Qed.

End lists.

#[global] Abbreviation list_findZ P := (list_findZ_from P 0).

NES.Begin std.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (it_ty ty : type).
  Implicit Types p : ptr.
  Import specify_notation. (** this should be enabled by default. Add to prelude? *)

  #[materialized]
  cpp.spec "std::find<$it_ty, $ty>($it_ty, $it_ty,const $ty &)"
    as find_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} BundledRep it_ty (C * Iter)%type
      \\requires HasRanges it_ty C Iter
      \\requires{V} BundledRep ty V
      \\requires  EqDecision V
      \\with
         \with c
         \arg{beginp : ptr} "begin" beginp
         \prepost{itb} beginp |-> objR it_ty 1$m (c, itb)

         \arg{endp : ptr} "end" endp
         \prepost{ite} endp |-> objR it_ty 1$m (c, ite)

         \arg{vpp : ptr} "v" vpp
         \prepost{vp : ptr} vpp |-> refR<ty> 1$m vp
         \prepost{vq v} vp |-> objR ty vq v

         (* spine and payload of the range between `begin` and `end` *)
         \prepost{q ps}    range it_ty c q itb ps ite
         \prepost{objq xs} payload it_ty c (fun x => objR ty objq x) ps xs
         \post{retp : ptr}[retp]
           ∃ itr,
             retp |-> objR it_ty 1$m (c, itr) **
             match list_findZ (eq v) xs with
             | Some (i, _) =>
                 lookup_result (ps !! i) itr
             | None => [| itr = ite |]
             end ).

  (* NOTE: in the argument list of [find_spec], we make the C++ types the explicit types and let
     the type class [BundledRep] infer the model type for each. *)
  #[global] Arguments find_spec tu {C Iter _IterRep _IterRanges} {T _TRep _TEq} : rename.

End with_cpp.

NES.End std.
