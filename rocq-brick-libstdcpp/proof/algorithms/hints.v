(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Export skylabs.brick.libstdcpp.algorithms.spec.

(** Automation for clients of [spec.v]. *)

(* [specify_raw] is what [predicate_call] unfolds to. *)
#[global] Hint Opaque specify_raw : sl_opacity.

NES.Begin std.

Section raw_pointer_iterators.
  Context `{Σ : cpp_logic, σ : genv}.

  (* <<T*>> over an array: the state is the array base and an index. *)
  #[global] Instance ptr_iter_rep ty : BundledRep (Tptr ty) (ptr * Z) | 100 :=
    {| objR q st := ptrR<ty> q (st.1 .[ ty ! st.2 ]) |}.
  #[global] Instance ptr_iter_ranges ty : HasRanges (Tptr ty) ptr Z | 100 :=
    array_ranges ty (Tptr ty).

  (* [typed_sliceR] is what survives of [array_spine] after a call. *)
  Lemma array_spine_of_typed_sliceR ty (basep : ptr) q i j :
    is_Some (size_of σ ty) ->
    basep |-> typed_sliceR ty i j |-- array_spine ty basep q i (rangeZ i j) j.
  Proof.
    intros Hsz. rewrite /array_spine. iIntros "#H".
    iDestruct (observe [| (i ≤ j)%Z |] with "H") as %Hij.
    do 3 (iSplit; first done).
    iSplit.
    - go $usenamed=true.
    - iApply big_sepL_intro. iIntros "!>" (k idx Hidx).
      apply lookup_rangeZ in Hidx as [Hb _].
      go $usenamed=true.
  Qed.

  (* Array to the spine and payload of a range over it; the fraction is free. *)
  #[program]
  Definition ptr_spine_intro_CB (ty : type) (basep : ptr) i j :=
    \cancelx
    \bound_existential q
    \proving array_spine ty basep q i (rangeZ i j) j
    \instantiate q := 1$m%cQp
    \bound A (R : A -> Rep)
    \proving{(vs : list A)} payload (Tptr ty) basep R (rangeZ i j) vs
    \through basep |-> array_sliceR ty i j R vs
    \end.
  Next Obligation.
    intros. iIntros "_" (q ? A R vs) "[-> A]".
    iDestruct (array_sliceR_eqv_spine_payload_rangeZ ty (Tptr ty) 1$m%cQp with "A") as "[$ $]".
  Qed.

  (* And back. *)
  #[program]
  Definition ptr_spine_elim_CF (ty : type) (basep : ptr) i j (_ : HasSize ty) :=
    \cancelx
    \preserving basep |-> typed_sliceR ty i j
    \with A (R : A -> Rep)
    \using{(vs : list A)} payload (Tptr ty) basep R (rangeZ i j) vs
    \deduce basep |-> array_sliceR ty i j R vs
    \end.
  Next Obligation.
    intros. iIntros "[#Ht Hp]". iSplitL; last done.
    iDestruct (array_spine_of_typed_sliceR ty basep 1$m%cQp i j with "Ht") as "Hs"; first done.
    iApply (array_sliceR_eqv_spine_payload_rangeZ ty (Tptr ty) 1$m%cQp). iFrame "Hs Hp".
  Qed.

  (* An iterator object holding [c0 .[ty ! k]], or [c0] itself as index 0. *)
  #[program]
  Definition ptr_iter_offset_C (ty : type) (p c0 : ptr) q k :=
    \cancelx
    \consuming p |-> ptrR<ty> q (c0 .[ty ! k])
    \proving{c i} p |-> ptrR<ty> q (c .[ty ! i])
    \through [| c = c0 |]
    \through [| i = k |]
    \end.
  Next Obligation.
    intros. iIntros "H" (c i) "[-> ->]". done.
  Qed.

  #[program]
  Definition ptr_iter_base_C (ty : type) (p c0 : ptr) q :=
    \cancelx
    \consuming p |-> ptrR<ty> q c0
    \proving{c i} p |-> ptrR<ty> q (c .[ty ! i])
    \through [| c = c0 |]
    \through [| i = 0%Z |]
    \through [| is_Some (size_of σ ty) |]
    \end.
  Next Obligation.
    intros. iIntros "H" (c i) "(-> & -> & %Hsz)".
    by rewrite offset_ptr_sub_0.
  Qed.

End raw_pointer_iterators.
#[global] Hint Resolve ptr_spine_intro_CB ptr_spine_elim_CF ptr_iter_offset_C : sl_opacity.
#[global] Hint Resolve ptr_iter_base_C | 200 : sl_opacity.

#[global] Hint Opaque predicate_call : sl_opacity.

(** [S] is the registered specification of the call operator of [pred_ty]. *)
Class CallableSpec `{Σ : cpp_logic} (pred_ty : type) (S : mpred) : Prop := {}.
#[global] Hint Mode CallableSpec - - - + - : typeclass_instances.

(** [predicate_call] follows in [tu] from the callable specification [S]. *)
Class PredicateCallFrom `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (S : mpred)
    (negated : bool) (it_ty pred_ty : type) {C : Set} {Iter P V : Type}
    `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
      !BundledRep pred_ty P, !Predicate pred_ty P V}
    (R : V -> Rep) : Prop :=
  predicate_call_from : denoteModule tu ⊢ □ S -∗ predicate_call negated it_ty pred_ty R.

(** [D] is what the adapter's body needs about the iterator type [it_ty] besides the
    translation unit, e.g. the specification of a library iterator's <<operator*>>. *)
Class IteratorDeps `{Σ : cpp_logic} (it_ty : type) (D : mpred) : Prop := {}.
#[global] Hint Mode IteratorDeps - - - + - : typeclass_instances.

(** [predicate_call] follows in [tu] from [S] and the iterator's [D]. *)
Class PredicateCallFromDeps `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (S D : mpred)
    (negated : bool) (it_ty pred_ty : type) {C : Set} {Iter P V : Type}
    `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
      !BundledRep pred_ty P, !Predicate pred_ty P V}
    (R : V -> Rep) : Prop :=
  predicate_call_from_deps :
    denoteModule tu ⊢ □ S -∗ □ D -∗ predicate_call negated it_ty pred_ty R.

(* Verifies the adapter's body against [tu], using [S] (and [D]). *)
#[global] Hint Extern 10 (PredicateCallFromDeps _ _ _ _ _ _ _) =>
  (unfold PredicateCallFromDeps;
   rewrite /predicate_call /predicate_call_body /ops_adapterR
     /ops_adapter_call /ops_adapter /=;
   verify_spec; go $usenamed=true; fail) : typeclass_instances.
#[global] Hint Extern 10 (PredicateCallFrom _ _ _ _ _ _) =>
  (unfold PredicateCallFrom;
   rewrite /predicate_call /predicate_call_body /ops_adapterR
     /ops_adapter_call /ops_adapter /=;
   verify_spec; go $usenamed=true; fail) : typeclass_instances.

Section callable.
  Context `{Σ : cpp_logic, σ : genv}.

  (** A caller that assumes the callable's specification [S] gets [predicate_call]. *)
  #[program]
  Definition predicate_call_from_C (tu : translation_unit) (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (R : V -> Rep) (S : mpred) (_ : CallableSpec pred_ty S)
      (Hcall : PredicateCallFrom tu S negated it_ty pred_ty R) :=
    \cancelx
    \preserving denoteModule tu
    \preserving □ S
    \proving predicate_call negated it_ty pred_ty R
    \end.
  Next Obligation.
    intros. iIntros "[#M #S]". iApply (predicate_call_from (PredicateCallFrom := Hcall) with "M S").
  Qed.

  #[program]
  Definition predicate_call_from_deps_C (tu : translation_unit) (negated : bool) (it_ty pred_ty : type)
      {C : Set} {Iter P V : Type}
      `{!BundledRep it_ty (C * Iter)%type, !HasRanges it_ty C Iter,
        !BundledRep pred_ty P, !Predicate pred_ty P V}
      (R : V -> Rep) (S D : mpred) (_ : CallableSpec pred_ty S) (_ : IteratorDeps it_ty D)
      (Hcall : PredicateCallFromDeps tu S D negated it_ty pred_ty R) :=
    \cancelx
    \preserving denoteModule tu
    \preserving □ S
    \preserving □ D
    \proving predicate_call negated it_ty pred_ty R
    \end.
  Next Obligation.
    intros. iIntros "(#M & #S & #D)".
    iApply (predicate_call_from_deps (PredicateCallFromDeps := Hcall) with "M S D").
  Qed.

  (* The element Rep and values of a range over a whole array are the array's. *)
  #[program]
  Definition array_sliceR_pick_C (ty : type) (basep : ptr) i j {A} (R0 : A -> Rep) (xs0 : list A) :=
    \cancelx
    \consuming basep |-> array_sliceR ty i j R0 xs0
    \bound_existential (R : A -> Rep)
    \bound_existential (xs : list A)
    \proving basep |-> array_sliceR ty i j R xs
    \instantiate R := R0
    \instantiate xs := xs0
    \end.
  Next Obligation. intros. iIntros "H" (R ? xs ?) "[%HR %Hxs]". subst. iExact "H". Qed.
End callable.
#[global] Hint Resolve predicate_call_from_C predicate_call_from_deps_C array_sliceR_pick_C : sl_opacity.

NES.End std.

(* Finds [S] for a class type from the [SpecFor] registration of its <<operator()>>. *)
Module algorithms_callable_spec.
  Import Ltac2.Ltac2.
  Ltac2 find (ty : constr) : unit :=
    lazy_match! ty with
    | Tnamed ?cls =>
        let nm := open_constr:(Nscoped $cls (Nop _ OOCall _)) in
        let x := Database.query "callable_spec" open_constr:(SpecFor.C (∅ : translation_unit) $nm) in
        lazy_match! Std.eval_whd_all x with
        | SpecFor.mk _ _ ?spec => Control.refine (fun () => open_constr:(std.Build_CallableSpec _ _ _ _ $spec))
        end
    end.
End algorithms_callable_spec.
#[global] Hint Extern 10 (std.CallableSpec ?ty _) =>
  (let f := ltac2:(ty |- algorithms_callable_spec.find (Option.get (Ltac1.to_constr ty))) in f ty)
  : typeclass_instances.
