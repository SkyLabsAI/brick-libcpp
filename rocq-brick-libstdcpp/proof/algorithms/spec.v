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

(** * <<std::all_of>>, <<std::any_of>>, <<std::none_of>>

    Generic in the iterator type (any [HasRanges]) and the predicate type. The result
    is [forallb], [existsb], [negb ∘ existsb] of [pred_test] over the range, with at
    most [length xs] predicate calls ([alg.all.of], [alg.any.of], [alg.none.of]).

    libstdc++ 12 calls the predicate only in <<__gnu_cxx::__ops::_Iter_pred>> /
    <<_Iter_negate>>; [PredicateCall] proves that call against the program's code.
    The rest of the algorithm is trusted, as for <<std::find>>.

    LIMITATION: iterator operations and copies of the predicate are trusted. The
    predicate may not modify the elements or keep state inside itself (use
    [pred_inv]). Exceptions, <<ExecutionPolicy>> overloads and <<std::ranges>> are
    not covered.

    NOTE: one section per [algorithms] subclause; a subclause that outgrows this file
    moves to <<proof/algorithms/<subclause>.v>>, re-exported here. *)

(** [pred_test p x]: the answer on [x]. [pred_inv p k]: state owned after [k] calls. *)
Class Predicate `{Σ : cpp_logic} (pred_ty : type) (Pred Elem : Type) : Type := {
  pred_test : Pred -> Elem -> bool;
  pred_inv : Pred -> Z -> mpred
}.
#[global] Arguments Predicate {_ _ _} pred_ty Pred Elem : assert.
#[global] Hint Mode Predicate - - - + - - : typeclass_instances.
#[global] Arguments pred_test {_ _ _} pred_ty {Pred Elem _} p x : assert.
#[global] Arguments pred_inv {_ _ _} pred_ty {Pred Elem _} p k : assert.

(** A predicate without effects. *)
Definition pure_predicate `{Σ : cpp_logic} {pred_ty : type} {Pred Elem : Type}
    (test : Pred -> Elem -> bool) : Predicate pred_ty Pred Elem :=
  {| pred_test := test; pred_inv _ _ := emp |}.

Section predicate_call.
  Context `{Σ : cpp_logic, σ : genv}.

  (** <<__gnu_cxx::__ops::_Iter_negate<pred_ty>>> or <<_Iter_pred<pred_ty>>>. *)
  Definition ops_adapter (negated : bool) (pred_ty : type) : name :=
    Ninst
      (Nscoped (Nscoped (Nglobal (Nid "__gnu_cxx"%pstring)) (Nid "__ops"%pstring))
         (Nid (if negated then "_Iter_negate"%pstring else "_Iter_pred"%pstring)))
      [Atype pred_ty].

  Definition ops_adapter_call (negated : bool) (it_ty pred_ty : type) : name :=
    Ninst
      (Nscoped (ops_adapter negated pred_ty) (Nop function_qualifiers.N OOCall [it_ty]))
      [Atype it_ty].

  Definition ops_adapterR (negated : bool) (pred_ty : type) {Pred : Type}
      `{!BundledRep pred_ty Pred} (q : cQp.t) (p : Pred) : Rep :=
    structR (ops_adapter negated pred_ty) q **
    _field (Nscoped (ops_adapter negated pred_ty) (Nid "_M_pred"%pstring)) |-> objR pred_ty q p.

  (** The [k]-th call, [k < length xs], on an element [x] of [xs]. *)
  Definition predicate_call_body (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (R : cQp.t -> V -> Rep) (p : P) (xs : list V) (this : ptr) :
      WpSpec mpred ptr ptr :=
    \arg{itp : ptr} "__it" itp
    \prepost{c i} itp |-> objR it_ty 1$m (c, i)
    \prepost{q x} dereference it_ty c i |-> R q x
    \require x ∈ xs
    \prepost this |-> ops_adapterR negated pred_ty 1$m p
    \with (k : Z)
    \require (0 <= k < lengthZ xs)%Z
    \pre pred_inv pred_ty p k
    \post{retp : ptr}[retp]
      retp |-> boolR 1$m (xorb negated (pred_test pred_ty p x)) **
      pred_inv pred_ty p (k + 1).

  Definition predicate_call (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (R : cQp.t -> V -> Rep) (p : P) (xs : list V) : mpred :=
    specify_raw
      {| info_name := ops_adapter_call negated it_ty pred_ty;
         info_type := tMethod (ops_adapter negated pred_ty) QM Tbool [it_ty] |}
      (predicate_call_body negated it_ty pred_ty R p xs).

  (** [predicate_call] proved from the program's code and from [pc_deps], library
      specifications the caller holds. *)
  Record PredicateCall (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (R : cQp.t -> V -> Rep) (p : P) (xs : list V) : Type := {
    pc_tu : translation_unit;
    pc_loaded : pc_tu ⊧ σ;
    pc_deps : mpred;
    pc_ok : denoteModule pc_tu ⊢ □ pc_deps -∗ predicate_call negated it_ty pred_ty R p xs
  }.
  #[global] Arguments pc_deps {_ _ _ _ _ _ _ _ _ _ _ _ _ _} _ : assert.
  #[global] Arguments Build_PredicateCall {_ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ : assert.
End predicate_call.

(** Proves [pc_ok] from [Hspec], the predicate's own verified specification.
    Needs the warning [sl-transparent-constants] disabled. *)
Ltac verify_predicate_call Hspec :=
  rewrite /predicate_call /predicate_call_body /ops_adapterR
    /ops_adapter_call /ops_adapter /=;
  verify_spec;
  iRename select (denoteModule _) into "Hmodule";
  iDestruct (Hspec with "Hmodule") as "#?";
  go $usenamed=true.

Section all_any_none_of.
  Context `{Σ : cpp_logic, σ : genv}.
  Import specify_notation.

  (** Shared by the three algorithms. *)
  Definition algorithm_spec (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (result : (V -> bool) -> list V -> bool) : WpSpec mpred ptr ptr :=
    \with c
    \arg{firstp : ptr} "first" firstp
    \prepost{itb} firstp |-> objR it_ty 1$m (c, itb)
    \arg{lastp : ptr} "last" lastp
    \prepost{ite} lastp |-> objR it_ty 1$m (c, ite)
    \arg{predp : ptr} "pred" predp
    \prepost{p} predp |-> objR pred_ty 1$m p
    \prepost{q ps} range it_ty c q itb ps ite
    \prepost{(R : cQp.t -> V -> Rep) objq xs} payload it_ty c (R objq) ps xs
    \with (call : PredicateCall negated it_ty pred_ty R p xs)
    \prepost □ pc_deps call
    \pre pred_inv pred_ty p 0
    \post{retp : ptr}[retp]
      retp |-> boolR 1$m (result (pred_test pred_ty p) xs) **
      ∃ k : Z, [| (0 <= k <= lengthZ xs)%Z |] ** pred_inv pred_ty p k.

  Context (it_ty pred_ty : type).

  #[materialized]
  cpp.spec "std::all_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as all_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} BundledRep it_ty (C * Iter)%type
      \\requires HasRanges it_ty C Iter
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\with \exact Reduce (algorithm_spec true it_ty pred_ty (fun test xs => forallb test xs)) ).

  #[materialized]
  cpp.spec "std::any_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as any_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} BundledRep it_ty (C * Iter)%type
      \\requires HasRanges it_ty C Iter
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\with \exact Reduce (algorithm_spec false it_ty pred_ty (fun test xs => existsb test xs)) ).

  #[materialized]
  cpp.spec "std::none_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as none_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} BundledRep it_ty (C * Iter)%type
      \\requires HasRanges it_ty C Iter
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\with \exact Reduce (algorithm_spec false it_ty pred_ty (fun test xs => negb (existsb test xs))) ).

  #[global] Arguments all_of_spec tu {C Iter _IterRep _IterRanges} {P _PredRep} {V _Pred} : rename.
  #[global] Arguments any_of_spec tu {C Iter _IterRep _IterRanges} {P _PredRep} {V _Pred} : rename.
  #[global] Arguments none_of_spec tu {C Iter _IterRep _IterRanges} {P _PredRep} {V _Pred} : rename.
End all_any_none_of.

NES.End std.
