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

Section pair_model.
  Context `{Σ : cpp_logic, σ : genv}.

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
End pair_model.





NES.End std.

(** * Registration *)

#[export] Hint Resolve std.ptr_spine_intro_CB std.ptr_spine_elim_CF std.ptr_iter_offset_C
  std.array_sliceR_pick_C std.pair_model_C : br_hints.
#[export] Hint Resolve std.ptr_spine_empty_C | 5 : br_hints.
#[export] Hint Resolve std.ptr_iter_base_C | 200 : br_hints.
#[export] Hint Resolve std.cptrR_weaken_C | 1000 : br_hints.

#[export] Hint Resolve std.calls_ok_True : pure.
(* On a concrete range, [calls_ok] unfolds to one precondition per tested element. *)
#[export] Hint Extern 10 (std.calls_ok _ _ _) => solve [simpl; repeat split; lia] : pure.
(* Proves the [fs_entails] side conditions of [cptrR_weaken_C] when [go] can; this runs a
   nested [go] on a specification entailment, which mentions no further callables. *)
#[export] Hint Extern 100 (fs_entails _ _) => solve [rewrite /fs_entails; go] : pure.
