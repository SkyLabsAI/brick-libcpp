Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.hints.alignment.
Require Import skylabs.auto.cpp.hints.find_spec skylabs.auto.cpp.hints.invoke skylabs.auto.cpp.hints.new_delete.
Require Import skylabs.brick.libstdcpp.new.inc_new_cpp.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.new.spec_exc.
Require Import skylabs.brick.libstdcpp.new.hints.

(** * Consistency of the <<operator new>>/<<operator delete>> specifications
    with the semantics of new- and delete-expressions

    These lemmas compose the library specifications with BRiCk's axioms for
    [Enew] and [Edelete]: the specifications provide exactly the resources the
    axioms demand, and the allocation receipt that is left over is packaged
    into the allocation token.

    NOTE: [wp_operand_new] (scalar form) does not state that the allocated type
    is not an array type, while the token indexes its receipt by
    [is_array_type]; hence the [is_array_type aty = false] premises. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{alignment_support : !allocation_alignment_support σ}.

  (** Unsequenced evaluation of two non-interfering computations (each
      producing a value without using resources or freeing anything) is
      independent of the evaluation order. *)
  Lemma nd_seqs_noninterfering2 {T} (m1 m2 : wp.WPE.M T) v1 v2 Q :
    (forall K, K v1 1%free ⊢ m1 K) -> (forall K, K v2 1%free ⊢ m2 K) ->
    Q [v1; v2] ((1 >*> 1) >*> 1)%free ⊢ wp.WPE.nd_seqs [m1; m2] Q.
  Proof.
    intros H1 H2. rewrite /wp.WPE.nd_seqs /=.
    iIntros "HQ" (pre post q Heq).
    destruct pre as [|a [|b pre]]; simplify_eq/=.
    - iApply H1. iIntros (pre0 post0 q0 Heq0).
      destruct pre0 as [|a0 pre0]; simplify_eq/=;
        last by destruct pre0; simplify_eq/=.
      iApply H2. rewrite /wp.WPE.Mret /=. iExact "HQ".
    - iApply H2. iIntros (pre0 post0 q0 Heq0).
      destruct pre0 as [|a0 pre0]; simplify_eq/=;
        last by destruct pre0; simplify_eq/=.
      iApply H1. rewrite /wp.WPE.Mret /=. iExact "HQ".
    - destruct pre; simplify_eq/=.
  Qed.
Context (ρ : region).

  Lemma wp_new_aligned_token aty oinit Q sz al :
    size_of σ aty = Some sz -> align_of aty = Some al ->
    valid<"unsigned long"> sz -> valid<"unsigned long"> al ->
    is_array_type aty = false ->
    denoteModule source ⊢ operator_new_align -∗
    (Forall storage obj : ptr, provides_storage storage obj aty -*
       letI* free' := wp_opt_initialize ρ source oinit aty obj in
       obj |-> alloc.tokenR_with_alignment aty (Some al) 1 -*
       Q (Vptr obj) (free' >*> ((1 >*> 1) >*> 1))%free) -*
    wp_operand source ρ
      (Enew ("operator new(unsigned long, enum std::align_val_t)"%cpp_name,
             "void*(unsigned long, enum std::align_val_t)"%cpp_type)
            [] (new_form.Allocating true) aty None oinit) Q.
  Proof.
    intros Hsz Hal Hv1 Hv2 Harr; have Hsup := supported_alignment_of_type _ _ Hal.
    iIntros "#M #S K".
    iDestruct (observe [| source ⊧ σ |] with "M") as %MOD.
    (* Anonymous: automation does not use named premises. *)
    iRevert "M S". iIntros "#? #?".
    iApply (wp_operand_new_glob source ρ _ _ _ true [] oinit aty _ Q).
    iExists sz, al. iSplit; first done. iSplit; first done.
    rewrite /wp_unmaterialized_args /=.
    (* The implicit size and alignment arguments do not interfere. *)
    iApply (nd_seqs_noninterfering2 _ _
      (Unmaterialized "unsigned long" (Vn sz))
      (Unmaterialized "enum std::align_val_t" (Vn al))).
    { intros K. rewrite /wp_call_initialize_val /=.
      iIntros "HK". iApply wp_operand_int. iSplit; [ by iPureIntro | iExact "HK" ]. }
    { intros K. rewrite /wp_call_initialize_val /=.
      iIntros "HK". iApply wp_operand_cast_integral. iApply wp_operand_int.
      iSplit; first by iPureIntro.
      iExists (Vn al). iFrame "HK". iPureIntro.
      rewrite /conv_int /=. split; first done.
      have := type.has_int_type_RL _ _ _ Hv2.
      rewrite /bitsize.bound /= => ?. by rewrite to_unsigned_bits_id; last lia. }
    go.
    iDestruct select (provides_storage _ _ _) as "Hps".
    iSpecialize ("K" with "Hps").
    iDestruct select (_ |-> allocatedR _ _ _ _)%I as "Rcpt".
    destruct oinit; simpl.
    - iApply (wp_initialize_frame source source with "[Rcpt] K"); first done.
      iIntros (f) "W ?". iApply "W". go. rewrite Harr. iFrame "Rcpt".
    - iApply (default_initialize_frame source source with "[Rcpt] K"); first done.
      iIntros (f) "W ?". iApply "W". go. rewrite Harr. iFrame "Rcpt".
  Qed.

End with_cpp.
