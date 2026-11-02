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
    is [forallb], [existsb], [negb ∘ existsb] of [pred_test] over the range
    ([alg.all.of], [alg.any.of], [alg.none.of]).

    The predicate is a higher-order argument: on a non-empty range, the specs require
    the callable to satisfy [predicate_contract] (via [pred_callable]), an abstract
    specification derived from the [Predicate] instance. Clients assume the callable's
    own specification, as with virtual calls ([vptrI]); the hints in [hints.v] reduce
    [pred_callable] to an entailment between the two specifications, which [go]
    usually proves when the callable's specification is close to the contract, and
    otherwise leaves to the client.

    libstdc++ 12 checks the elements in order and stops at the first one that decides
    the result, so the predicate is called exactly on [tested_prefix]. The specs
    expose that history through [pred_inv]. The calls go through
    <<__gnu_cxx::__ops::_Iter_pred>> / <<_Iter_negate>>, which are trusted together
    with the rest of the algorithm, as for <<std::find>>.

    LIMITATION: iterator operations, and copies and moves of the predicate (which must
    preserve its model), are trusted. The predicate's call operator must return
    <<bool>> and take the element either by value, for a type with [PrimVal], or by
    reference (see [PredicateArg]). For a class, the call operator is the one whose
    specification is registered, which is trusted to be the one overload resolution
    picks. Exceptions, <<ExecutionPolicy>> overloads and <<std::ranges>> are not
    covered.

    NOTE: one section per [algorithms] subclause; a subclause that outgrows this file
    moves to <<proof/algorithms/<subclause>.v>>, re-exported here. *)

(** [Predicate pred_ty P V] describes a callable of C++ type [pred_ty], with model
    [P], on elements with model [V]:
    - [pred_test p x] is its answer on [x];
    - [pred_pre p hist x] must hold for calling it on [x], after the calls on [hist],
      to be defined: e.g. the call would otherwise divide by zero, overflow, or run out
      of space to record [x];
    - [pred_inv p hist] is what the predicate owns after it was called, in order, on
      the elements [hist]. *)
Class Predicate `{Σ : cpp_logic} (pred_ty : type) (Pred Elem : Type) : Type := {
  pred_test : Pred -> Elem -> bool;
  pred_pre : Pred -> list Elem -> Elem -> Prop;
  pred_inv : Pred -> list Elem -> mpred
}.
#[global] Arguments Predicate {_ _ _} pred_ty Pred Elem : assert.
#[global] Hint Mode Predicate - - - + - - : typeclass_instances.
#[global] Arguments pred_test {_ _ _} pred_ty {Pred Elem _} p x : assert.
#[global] Arguments pred_pre {_ _ _} pred_ty {Pred Elem _} p hist x : assert.
#[global] Arguments pred_inv {_ _ _} pred_ty {Pred Elem _} p hist : assert.

(** A predicate without effects, defined on all elements. *)
Definition pure_predicate `{Σ : cpp_logic} {pred_ty : type} {Pred Elem : Type}
    (test : Pred -> Elem -> bool) : Predicate pred_ty Pred Elem :=
  {| pred_test := test; pred_pre _ _ _ := True; pred_inv _ _ := emp |}.

(** The elements [stop] is called on when scanning [xs] in order, stopping at the first
    one where it returns [true]. *)
Fixpoint tested_prefix {A} (stop : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs => if stop x then [x] else x :: tested_prefix stop xs
  end.

(** [pre done x] holds for each [x] of [xs], where [done] are the elements before it. *)
Fixpoint calls_ok {A} (pre : list A -> A -> Prop) (done xs : list A) : Prop :=
  match xs with
  | [] => True
  | x :: xs => pre done x /\ calls_ok pre (done ++ [x]) xs
  end.

Lemma calls_ok_True {A} (done xs : list A) : calls_ok (fun _ _ => True) done xs.
Proof. by elim: xs done. Qed.

Section predicate_contract.
  Context `{Σ : cpp_logic, σ : genv}.
  Import specify_notation.

  (** [PredicateArg param_ty V] passes an element to a parameter of type [param_ty].
      [pred_argR i] is the representation the algorithm requires of the elements, for
      some index [i : pred_arg_idx]. *)
  Class PredicateArg (param_ty : type) (V : Type) : Type := {
    pred_arg_idx : Type;
    pred_arg_default : pred_arg_idx;
    pred_argR : pred_arg_idx -> V -> Rep;
    pred_arg : pred_arg_idx -> V -> WpSpec mpred val val -> WpSpec mpred val val
  }.
  #[global] Arguments pred_arg_idx param_ty {V _} : assert.
  #[global] Arguments pred_arg_default param_ty {V _} : assert.
  #[global] Arguments pred_argR param_ty {V _} i x : assert.
  #[global] Arguments pred_arg param_ty {V _} i x K : assert.

  (** By reference: the callee borrows the element, in any representation. *)
  #[global] Instance PredicateArg_ref ty V : PredicateArg (Tref ty) V | 10 :=
    {| pred_arg_idx := V -> Rep;
       pred_arg_default _ := emp;
       pred_argR R := R;
       pred_arg R x K := \arg{a} "x" (Vref a) \prepost a |-> R x \exact K |}.

  (** By value: the elements must be primitive values, which the call copies. *)
  #[global] Instance PredicateArg_val ty V `{!PrimVal ty V} : PredicateArg ty V | 20 :=
    {| pred_arg_idx := cQp.t;
       pred_arg_default := 1$m%cQp;
       pred_argR q x := primR ty q (Vinj ty x);
       pred_arg _ x K := \arg "x" (Vinj ty x) \exact K |}.

  (** [PredicateCallable pred_ty P param_ty]: a call on a [pred_ty] object with model
      [p] satisfies [S] when [pred_callable p S] holds. The call takes the element as
      [param_ty]. *)
  Class PredicateCallable (pred_ty : type) (P : Type) (param_ty : type) : Type := {
    pred_callable : P -> WpSpec mpred val val -> mpred
  }.
  #[global] Arguments pred_callable pred_ty {P param_ty _} p S : assert.

  (** A class with a call operator [nm]: [this] holds the object. The instance is found
      by the [Hint Extern] below. *)
  Definition member_callable (cls : name) (nm : obj_name) (tq : type_qualifiers)
      (param_ty : type) {P} `{!BundledRep (Tnamed cls) P} : PredicateCallable (Tnamed cls) P param_ty :=
    {| pred_callable p S :=
         _global nm |-> unmaterialized_specR (tMethod cls tq Tbool [param_ty])
           (fun this : ptr => \prepost this |-> objR (Tnamed cls) 1$m p \exact S) |}.

  (** A function pointer: its model is the function it points to. *)
  #[global] Instance fptr_callable cc ar param_ty :
      PredicateCallable (Tptr (Tfunction (@FunctionType _ cc ar Tbool [param_ty]))) ptr param_ty :=
    {| pred_callable fp S := fp |-> unmaterialized_specR (@tFunction cc Tbool ar [param_ty]) S |}.

  (** The abstract specification of one call on [x], after the calls on [hist]. *)
  Definition predicate_contract (pred_ty : type) {param_ty : type} {P V : Type}
      `{!Predicate pred_ty P V, !PredicateArg param_ty V}
      (i : pred_arg_idx param_ty) (p : P) : WpSpec mpred val val :=
    \with (x : V) (hist : list V)
    \exact pred_arg param_ty i x (
      \require pred_pre pred_ty p hist x
      \pre pred_inv pred_ty p hist
      \post[Vbool (pred_test pred_ty p x)] pred_inv pred_ty p (hist ++ [x])).
End predicate_contract.

(** Finds the call operator <<cls::operator()(param_ty)>> from its registered
    specification, which clients assume. *)
Module predicate_callable.
  Import Ltac2.Ltac2.
  Ltac2 find (cls : constr) : unit :=
    let nm := open_constr:(Nscoped $cls (Nop _ OOCall [_])) in
    let x := Database.query "predicate_callable" open_constr:(SpecFor.C (∅ : translation_unit) $nm) in
    lazy_match! Constr.type x with
    | SpecFor.C _ ?op =>
        lazy_match! op with
        | Nscoped _ (Nop ?fq OOCall [?param_ty]) =>
            Control.refine (fun () =>
              constr:(member_callable $cls $op (function_qualifiers.to_type_qualifiers $fq) $param_ty))
        end
    end.
End predicate_callable.
#[global] Hint Extern 10 (PredicateCallable (Tnamed ?cls) _ _) =>
  (let f := ltac2:(cls |- predicate_callable.find (Option.get (Ltac1.to_constr cls))) in f cls)
  : typeclass_instances.

(** [IterState it_ty C Iter M]: an iterator of type [it_ty] at position [i] of
    collection [c] (see [HasRanges]) has model [iter_state c i], in the iterator's own
    [BundledRep]. *)
Class IterState (it_ty : type) (C : Set) (Iter M : Type) := iter_state : C -> Iter -> M.
#[global] Hint Mode IterState + + + + : typeclass_instances.
#[global] Arguments iter_state it_ty {C Iter M _} c i : assert.

(** Iterators modeled by their position, e.g. <<std::vector>>'s. *)
#[global] Instance pair_IterState it_ty C Iter : IterState it_ty C Iter (C * Iter) | 100 := pair.

Section all_any_none_of.
  Context `{Σ : cpp_logic, σ : genv}.
  Import specify_notation.

  (** Shared by the three algorithms. libstdc++ looks for the first element on which
      [xorb negated ∘ pred_test p] holds. *)
  Definition algorithm_spec (negated : bool) (it_ty pred_ty param_ty : type)
      {C : Set} {Iter M P V : Type}
      `{!HasRanges it_ty C Iter, !BundledRep it_ty M, !IterState it_ty C Iter M,
        !BundledRep pred_ty P, !Predicate pred_ty P V,
        !PredicateCallable pred_ty P param_ty, !PredicateArg param_ty V}
      (result : (V -> bool) -> list V -> bool) : WpSpec mpred ptr ptr :=
    \with c
    \arg{firstp : ptr} "first" firstp
    \prepost{itb} firstp |-> objR it_ty 1$m (iter_state it_ty c itb)
    \arg{lastp : ptr} "last" lastp
    \prepost{ite} lastp |-> objR it_ty 1$m (iter_state it_ty c ite)
    \arg{predp : ptr} "pred" predp
    \pre{p} predp |-> objR pred_ty 1$m p
    \prepost{q ps} range it_ty c q itb ps ite
    \prepost{(i : pred_arg_idx param_ty) xs} payload it_ty c (pred_argR param_ty i) ps xs
    (* An empty range calls nothing. *)
    (* An empty range calls nothing; its elements' representation is irrelevant. *)
    \persist match xs with
             | [] => [| i = pred_arg_default param_ty |]
             | _ => pred_callable pred_ty p (predicate_contract pred_ty i p)
             end
    \require calls_ok (pred_pre pred_ty p) []
      (tested_prefix (fun x => xorb negated (pred_test pred_ty p x)) xs)
    \pre pred_inv pred_ty p []
    \post{retp : ptr}[retp]
      retp |-> boolR 1$m (result (pred_test pred_ty p) xs) **
      (* The parameter was moved from. *)
      (∃ p', predp |-> objR pred_ty 1$m p') **
      pred_inv pred_ty p (tested_prefix (fun x => xorb negated (pred_test pred_ty p x)) xs).

  Context (it_ty pred_ty : type).

  #[materialized]
  cpp.spec "std::all_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as all_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} HasRanges it_ty C Iter
      \\requires{M} BundledRep it_ty M
      \\requires IterState it_ty C Iter M
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\requires{param_ty} PredicateCallable pred_ty P param_ty
      \\requires PredicateArg param_ty V
      \\with \exact Reduce (algorithm_spec true it_ty pred_ty param_ty (fun test xs => forallb test xs)) ).

  #[materialized]
  cpp.spec "std::any_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as any_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} HasRanges it_ty C Iter
      \\requires{M} BundledRep it_ty M
      \\requires IterState it_ty C Iter M
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\requires{param_ty} PredicateCallable pred_ty P param_ty
      \\requires PredicateArg param_ty V
      \\with \exact Reduce (algorithm_spec false it_ty pred_ty param_ty (fun test xs => existsb test xs)) ).

  #[materialized]
  cpp.spec "std::none_of<$it_ty, $pred_ty>($it_ty, $it_ty, $pred_ty)"
    as none_of_spec
    from inc_algorithms_cpp.source
    templates inc_algorithms_cpp_templates.templates
    ( \\requires{C Iter} HasRanges it_ty C Iter
      \\requires{M} BundledRep it_ty M
      \\requires IterState it_ty C Iter M
      \\requires{P} BundledRep pred_ty P
      \\requires{V} Predicate pred_ty P V
      \\requires{param_ty} PredicateCallable pred_ty P param_ty
      \\requires PredicateArg param_ty V
      \\with \exact Reduce (algorithm_spec false it_ty pred_ty param_ty (fun test xs => negb (existsb test xs))) ).

  #[global] Arguments all_of_spec tu {C Iter _IterRanges} {M _IterRep _IterState} {P _PredRep} {V _Pred}
    {param_ty _Callable _Arg} : rename.
  #[global] Arguments any_of_spec tu {C Iter _IterRanges} {M _IterRep _IterState} {P _PredRep} {V _Pred}
    {param_ty _Callable _Arg} : rename.
  #[global] Arguments none_of_spec tu {C Iter _IterRanges} {M _IterRep _IterState} {P _PredRep} {V _Pred}
    {param_ty _Callable _Arg} : rename.
End all_any_none_of.

NES.End std.
