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

NES.Begin std.

Section raw_pointer_iterators.
  Context `{Σ : cpp_logic, σ : genv}.

  (* <<T*>> over an array: positions are the array base and an index. *)
  #[global] Instance ptr_iter_ranges ty : HasRanges (Tptr ty) ptr Z | 100 :=
    array_ranges ty (Tptr ty).
  (* The iterator itself is the pointer [basep .[ ty ! i ]], with the builtin
     [BundledRep] for pointers. *)
  #[global] Instance ptr_IterState ty : IterState (Tptr ty) ptr Z ptr :=
    fun basep i => basep .[ ty ! i ].

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

  (* The spine of an empty range; [q] is irrelevant. *)
  #[program]
  Definition ptr_spine_empty_C (ty : type) (basep : ptr) i j (_ : TCEq i j) :=
    \cancelx
    \bound_existential q
    \proving array_spine ty basep q i (rangeZ i j) j
    \instantiate q := 1$m%cQp
    \through [| is_Some (size_of σ ty) |]
    \through valid_ptr (basep .[ ty ! j ])
    \end.
  Next Obligation.
    intros * Hij%TCEq_eq; subst. iIntros "_" (q ?) "(-> & %Hsz & #V)".
    rewrite /array_spine rangeZ_oob; last lia.
    iSplit; first by iPureIntro; lia. do 2 (iSplit; first done). by iSplit.
  Qed.

  (* The element Rep and values of a slice are the context's; the end bound is checked
     separately. *)
  #[program]
  Definition array_sliceR_pick_C (ty : type) (basep : ptr) i j {A} (R0 : A -> Rep) (xs0 : list A) :=
    \cancelx
    \consuming basep |-> array_sliceR ty i j R0 xs0
    \bound_existential (R : A -> Rep)
    \bound_existential (xs : list A)
    \proving{j'} basep |-> array_sliceR ty i j' R xs
    \instantiate R := R0
    \instantiate xs := xs0
    \through [| j' = j |]
    \end.
  Next Obligation. intros. iIntros "H" (R ? xs ? j') "(-> & -> & ->)". iExact "H". Qed.

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
#[global] Hint Resolve ptr_spine_intro_CB ptr_spine_elim_CF ptr_iter_offset_C array_sliceR_pick_C : sl_opacity.
#[global] Hint Resolve ptr_spine_empty_C | 5 : sl_opacity.
#[global] Hint Resolve ptr_iter_base_C | 200 : sl_opacity.

Section spec_entailment.
  Context `{Σ : cpp_logic, σ : genv}.

  (** A function pointer [p] with specification [fs] satisfies any specification
      [fs'] that [fs] entails. This applies to the higher-order requirements
      ([pred_callable]) of the algorithms: [p] is the callable, [fs] the specification
      the client assumes for it, and [fs'] the contract the algorithm needs.

      It leaves the entailment [fs_entails fs fs'] as a side condition, which [go]
      proves when [fs] is close enough to [fs'] (see the [pure] hint below); otherwise
      it stays in the goal for the client. Exact matches are found by [find_cptrR]
      first. *)
  #[program]
  Definition cptrR_weaken_C (p : ptr) fs' P fs
      (FS : find_spec.FindSpec σ false p P fs) :=
    \cancelx
    \preserving P
    \proving p |-> cptrR fs'
    \through [| fs_entails fs fs' |]
    \end.
  Next Obligation.
    intros. iIntros "P".
    iDestruct (find_spec._spec_ok FS with "[P]") as "#X"; first by destruct b => //=.
    iFrame "P". iIntros "%E". iPoseProof E as "#I".
    iPoseProof (_at_mono (p:=p) _ _ (cptrR_fs_impl fs fs') with "[]") as "W".
    { by rewrite _at_pureR. }
    by iApply (_at_wand with "W X").
  Qed.
End spec_entailment.
#[global] Hint Resolve cptrR_weaken_C | 1000 : sl_opacity.

(** [UniqueModel A v]: [v] is the only value of [A], e.g. [tt], or the model of a
    class without fields generated by <<cpp.class>>. *)
Class UniqueModel (A : Type) (v : A) : Prop := unique_model : ∀ x : A, x = v.
#[global] Hint Mode UniqueModel + - : typeclass_instances.
#[global] Instance unit_UniqueModel : UniqueModel unit tt.
Proof. by intros []. Qed.

(* Inductives with a single constant constructor: [destruct] leaves one goal, which
   picks [v]; any other type leaves goals that [reflexivity] cannot close. *)
#[global] Hint Extern 10 (UniqueModel _ _) =>
  (unfold UniqueModel; solve [let x := fresh in intros x; destruct x; reflexivity])
  : typeclass_instances.

Section unique_model.
  Context `{Σ : cpp_logic, σ : genv}.

  (** A model with a unique value, e.g. of a stateless predicate, is determined by its
      type, but representations such as <<cpp.class>>'s for a class without fields
      drop it when unfolded: e.g. the [\prepost{q m} other |-> R q m] of a generated
      copy constructor would leave [m] unbound. Pick the context's value if there is
      one (it may differ syntactically from [v]), and [v] otherwise. *)
  #[program]
  Definition unique_model_frac_C (p : ptr) {A} (R : cQp.t -> A -> Rep) (v : A) (_ : UniqueModel A v) :=
    \cancelx
    \bound q
    \bound_existential x
    \proving p |-> R q x
    \instantiate x := v
    \through p |-> R q v
    \end.
  Next Obligation. intros. iIntros "_" (q x ?) "[-> $]". Qed.

  #[program]
  Definition unique_model_frac_ctx_C (p : ptr) {A} (R : cQp.t -> A -> Rep) (v : A) (_ : UniqueModel A v) q0 y :=
    \cancelx
    \preserving p |-> R q0 y
    \bound q
    \bound_existential x
    \proving p |-> R q x
    \instantiate x := y
    \through p |-> R q y
    \end.
  Next Obligation. intros. iIntros "$" (q x ?) "[-> $]". Qed.

  (** A pair-valued model read through projections, as for <<std::vector>>'s iterators
      ([R st.1 st.2]), is the pair of what the context holds. *)
  #[program]
  Definition pair_model_C (p : ptr) {A B} (R : A -> B -> Rep) (a : A) (b : B) :=
    \cancelx
    \consuming p |-> R a b
    \bound_existential (x : A * B)
    \proving p |-> R x.1 x.2
    \instantiate x := (a, b)
    \end.
  Next Obligation. intros. iIntros "H" (x ?) "->". iExact "H". Qed.
End unique_model.

#[global] Hint Resolve unique_model_frac_ctx_C pair_model_C | 0 : sl_opacity.
#[global] Hint Resolve unique_model_frac_C | 1 : sl_opacity.


#[global] Hint Resolve calls_ok_True : pure.
(* On a concrete range, [calls_ok] unfolds to one precondition per tested element. *)
#[global] Hint Extern 10 (calls_ok _ _ _) => solve [simpl; repeat split; lia] : pure.

(** Proves the [fs_entails] side conditions of [cptrR_weaken_C] when [go] can. *)
#[global] Hint Extern 100 (fs_entails _ _) => solve [rewrite /fs_entails; go] : pure.

NES.End std.
