
Require Import skylabs.brick.libstdcpp.test.existing_specs.mutex_recursive_cpp.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.new.spec.

Section phase_b_final.
  Context `{Σ : mpred.LC.cpp_logic}.
  Context {σ : genv.genv}.
  Context (MOD : genv.genv_compat mutex_recursive_cpp.source σ).
  Context (STD_THREADS : HasStdThreads Σ).
  #[local] Existing Instance STD_THREADS.
  Context (LOCKED : recursive_mutex.lockedG Σ).
  #[local] Existing Instance LOCKED.
  Context (RM_OWN : own.HasOwn mpred.mpredI recursive_mutex.cmraR).
  #[local] Existing Instance RM_OWN.

  cpp.spec "unlocked_lifecycle_oracle()" from mutex_recursive_cpp.source
    as lifecycle_spec_v3 with (\post[Vbool true] emp).
  cpp.spec "base_recursive_protocol_oracle()" from mutex_recursive_cpp.source
    as base_protocol_spec_v3 with (\post[Vbool true] emp).
  cpp.spec "derived_recursive_protocol_oracle()" from mutex_recursive_cpp.source
    as derived_protocol_spec_v3 with (\post[Vbool true] emp).
  cpp.spec "basic_lockable_alternative_oracle()" from mutex_recursive_cpp.source
    as alternative_protocol_spec_v3 with (\post[Vbool true] emp).

  Section base_selection.
    #[local] Remove Hints
      recursive_mutex.ctor_spec'_spec_instance
      recursive_mutex.lock_spec'_spec_instance
      recursive_mutex.unlock_spec'_spec_instance
      recursive_mutex.lock_spec_alt'_spec_instance
      recursive_mutex.unlock_spec_alt'_spec_instance
      : typeclass_instances.
Lemma lifecycle_oracle_ok :
  verify[mutex_recursive_cpp.source] lifecycle_spec_v3.

Proof using LOCKED MOD STD_THREADS _Σ thread_info Σ σ.

verify_spec.

go $usenamed=true.

wp_while (fun ρ =>
  Exists p,
    _local ρ "mutex" |-> ptrR<"std::recursive_mutex"> 1$m p **
    (if bool_decide (p = nullptr) then emp else
       Exists (storage : ptr) (g : recursive_mutex.gname),
         storage |-> allocatedR 1 40 **
         p |-> recursive_mutex.R g 1$m **
         recursive_mutex.token g 1 **
         recursive_mutex.used_threads g ∅ **
         p |-> new_token.R 1
           {| new_token.alloc_ty := "std::recursive_mutex";
              new_token.storage_ptr := storage;
              new_token.overhead := 0 |}))%I.

go $usenamed=true.

1: iExists (1$m)%cQp; iFrame.

case_bool_decide.

2: go $usenamed=true.

2: iExists (1$m)%cQp; iFrame.

2: iExists ∅; iFrame.

2: iIntros "Hblock"; go $usenamed=true.

2: case_bool_decide.

2: subst storage; go $usenamed=true.

2: go $usenamed=true.

rewrite H.

go $usenamed=true.

case_bool_decide.

1: rewrite H; go $usenamed=true.

go $usenamed=true.

Qed.

Lemma base_protocol_oracle_ok :
  verify[mutex_recursive_cpp.source] base_protocol_spec_v3.
Proof using LOCKED MOD RM_OWN STD_THREADS _Σ thread_info Σ σ.

verify_spec.

wname [PostCond] "Hpost". iEval (rewrite (PC_ok PostCond)) in "Hpost".

go $usenamed=true.

iExists (1$m)%cQp, (1 / 2)%Qp, (recursive_mutex.token t (1 / 2) ∗ recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 1 ∗ protected_value_addr |-> intR 1$m 0)%I.

iFrame.

iFrame.

iDestruct select (recursive_mutex.token t 1) as "Htoken".

iDestruct "Htoken" as "[Htoken1 Htoken2]".

iFrame "Htoken1".

iDestruct select (recursive_mutex.used_threads t ∅) as "Hused". iDestruct select (protected_value_addr |-> intR 1$m 0) as "Hvalue". iSplitL "Htoken2 Hused Hvalue".

1: iAcIntro.

1: rewrite /commit_acc /=.

1: iMod (recursive_mutex.use_thread thr t ∅ with "Hused") as "[Hused Hlocked]"; first set_solver.

1: iApply fupd_mask_intro; first set_solver.

1: (iIntros "Hclose"; iExists 0; iFrame "Hlocked"; iIntros "HlockedS"; iMod "Hclose" as "_"; iFrame).

1: (iModIntro; done).

iIntros "(HR & (Htoken & Hused & Hlocked & Hvalue) & Hgiven1)". go $usenamed=true.

iExists (1$m)%cQp, (1 / 2)%Qp, (recursive_mutex.given_token t (1 / 2) ∗ recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 2 ∗ protected_value_addr |-> intR 1$m 1)%I. iFrame "HR Htoken". iDestruct select (protected_value_addr |-> intR 1$m 1) as "Hvalue". iSplitL "Hgiven1 Hused Hlocked Hvalue".
 1: iAcIntro. 1: rewrite /commit_acc /=. 1: iApply fupd_mask_intro; first set_solver.

1: (iIntros "Hclose"; iExists 1; iFrame "Hlocked"; iIntros "HlockedS"; iMod "Hclose" as "_"; iFrame). 1: (iModIntro; done).

iIntros "(HR & (Hgiven1 & Hused & Hlocked & Hvalue) & Hgiven2)". go $usenamed=true.

iExists (1$m)%cQp, (recursive_mutex.given_token t (1 / 2) ∗ recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 1 ∗ protected_value_addr |-> intR 1$m (1 + 2))%I. iFrame "HR". iDestruct select (protected_value_addr |-> intR 1$m (1 + 2)) as "Hvalue". iSplitL "Hgiven2 Hused Hlocked Hvalue".
 1: iAcIntro. 1: rewrite /commit_acc /=. 1: iApply fupd_mask_intro; first set_solver. 1: (iIntros "Hclose"; iExists 1; iFrame "Hlocked"; iIntros "HlockedS"; iMod "Hclose" as "_"; iFrame). 1: (iModIntro; done).

iIntros "(HR & Htoken1 & Hgiven & Hused & Hlocked & Hvalue)". go $usenamed=true.

iExists (1$m)%cQp, (recursive_mutex.token t (1 / 2) ∗ recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 0 ∗ protected_value_addr |-> intR 1$m (1 + 2 + 4))%I. iFrame "HR". iDestruct select (protected_value_addr |-> intR 1$m (1 + 2 + 4)) as "Hvalue". iSplitL "Htoken1 Hused Hlocked Hvalue".
 1: iAcIntro. 1: rewrite /commit_acc /=. 1: iApply fupd_mask_intro; first set_solver. 1: (iIntros "Hclose"; iExists 0; iFrame "Hlocked"; iIntros "Hlocked0"; iMod "Hclose" as "_"; iFrame). 1: (iModIntro; done).

iIntros "(HR & Htoken1 & Htoken2 & Hused & Hlocked & Hvalue)". iCombine "Htoken1 Htoken2" as "Htoken". go $usenamed=true.

iExists (1$m)%cQp, 1%Qp, (recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 1 ∗ protected_value_addr |-> intR 1$m (1 + 2 + 4))%I. iFrame "HR Htoken". iSplitL "Hused Hlocked Hvalue".

1: iAcIntro. 1: rewrite /commit_acc /=. 1: iApply fupd_mask_intro; first set_solver. 1: (iIntros "Hclose"; iExists 0; iFrame "Hlocked"; iIntros "HlockedS"; iMod "Hclose" as "_"; iFrame). 1: (iModIntro; done).

iIntros "(HR & (Hused & Hlocked & Hvalue) & Hgiven)". go $usenamed=true.

1: (iExists (1$m)%cQp; iFrame; done).

iDestruct select (snapshot_addr |-> intR 1$c (1 + 2 + 4)) as "Hsnapshot". iExists (1$m)%cQp, (recursive_mutex.used_threads t (∅ ∪ {[thr]}) ∗ recursive_mutex.locked t thr 0 ∗ protected_value_addr |-> intR 1$m (1 + 2 + 4))%I. iFrame "HR". iSplitL "Hused Hlocked Hvalue".

1: iAcIntro. 1: rewrite /commit_acc /=. 1: iApply fupd_mask_intro; first set_solver. 1: (iIntros "Hclose"; iExists 0; iFrame "Hlocked"; iIntros "Hlocked0"; iMod "Hclose" as "_"; iFrame). 1: (iModIntro; done).

iIntros "(HR & Htoken & Hused & Hlocked & Hvalue)".
simpl in *.

iEval (simpl) in "Hsnapshot". iEval (simpl) in "Hvalue".

have Heq : (1 + 2 + 4)%Z = 7%Z by lia.

iEval (rewrite Heq) in "Hsnapshot". iEval (rewrite Heq) in "Hvalue".

go $usenamed=true.

1: (iExists (1$c)%cQp; iFrame; done). iExists (∅ ∪ {[thr]}). iFrame "Hused". iNext. iApply ("Hpost" $! p). iFrame.

rewrite prim._at_tptsto_fuzzyR_Vbool_primR. iFrame.

Qed.
End base_selection.

Section derived_primary_selection.

#[local] Remove Hints recursive_mutex.ctor_spec_spec_instance recursive_mutex.lock_spec_spec_instance recursive_mutex.unlock_spec_spec_instance recursive_mutex.lock_spec_alt'_spec_instance recursive_mutex.unlock_spec_alt'_spec_instance : typeclass_instances.

Context (RM_IOWN : HasOwn (iPropI _Σ) recursive_mutex.cmraR).

Existing Instance RM_IOWN.

Definition selected_derived_ctor : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::recursive_mutex()" := ltac:(typeclasses eauto).

Definition selected_derived_lock : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::lock()" := ltac:(typeclasses eauto).

Definition selected_derived_unlock : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::unlock()" := ltac:(typeclasses eauto).

Definition derived_protocol_spec : mpredI := specify {| info_name := "derived_recursive_protocol_oracle()"; info_type := tFunction "bool" [] |} (\post[Vbool true] emp).

Theorem derived_protocol_oracle_ok : denoteModule mutex_recursive_cpp.source ⊢ ▷ recursive_mutex.ctor_spec' ∗ ▷ recursive_mutex.dtor_spec ∗ ▷ recursive_mutex.lock_spec' ∗ ▷ recursive_mutex.unlock_spec' -∗ derived_protocol_spec.
Proof using LOCKED MOD RM_IOWN STD_THREADS _Σ thread_info Σ σ.

unfold derived_protocol_spec.

verify_spec.

go $usenamed=true.

wname [protected_value_addr |-> intR 1$m 5] "Hvalue".

iExists [tele], emp%I, ().

iSplitR. { done. }

iSplitR. { iPureIntro. intros a. apply emp_weakly_objective. }

iIntros "(%g & HR & Htoken & Hused & Hinv)".
iDestruct "Hinv" as "#Hinv".

wname [current_thread thr] "Hthread".

iMod (recursive_mutex.use_thread_acquirable (TT := [tele]) thr g ∅ emp%I with "[$Hthread $Hused]") as "[Hused Hacq]"; first set_solver.

go $usenamed=true.

wname [mutex_addr |-> recursive_mutex.R (recursive_mutex.lock_gname g) 1$m] "HR".

iDestruct "Htoken" as "[Htoken1 Htoken2]".

iExists (1$m)%cQp, ((1 / 2)%Qp). iFrame "HR Htoken1".

iIntros "(HR & Hgiven1 & %n & %Hstep & Hacq)".

go $usenamed=true.

iExists (1$m)%cQp, (recursive_mutex.Held n args), ((1 / 2)%Qp). iFrame "HR Htoken2".

go $usenamed=true.

iExists (1$m)%cQp, args. go $usenamed=true.

iExists (1$m)%cQp. iFrame.

iExists (1$m)%cQp, _, _.

go $usenamed=true.

wname [recursive_mutex.acquireable g thr (recursive_mutex.release (recursive_mutex.Held n args)) emp] "Hacq".

iEval (rewrite -b0) in "Hacq".

iFrame "Hacq".

wname [recursive_mutex.token (recursive_mutex.lock_gname g) (1 / 2)] "Htoken1".

iIntros "(HR & Htoken2 & Hacq)".

iCombine "Htoken1 Htoken2" as "Htoken".

iEval (rewrite -b) in "Hacq".

go $usenamed=true.

iExists (1$m)%cQp, (1%Qp). iFrame "HR Htoken".

iIntros "(HR & Hgiven & %nfinal & %Hstepfinal & Hacq)".

go $usenamed=true.

iExists (1$m)%cQp, args. go $usenamed=true.

iExists (1$c)%cQp. iFrame.

wname [p |-> boolR 1$m (bool_decide ((5 * 2 + 3 + 7)%Z = 20%Z))] "Hret".

iEval (simpl) in "Hret".

iExists (∅ ∪ {[thr]}). iFrame "Hused".

iNext.

wname [bi_forall] "Hpost".

iApply ("Hpost" $! p).

rewrite prim._at_tptsto_fuzzyR_Vbool_primR. iFrame "Hret".
Qed.

End derived_primary_selection.

Section derived_alt_selection.

#[local] Remove Hints recursive_mutex.ctor_spec_spec_instance recursive_mutex.lock_spec_spec_instance recursive_mutex.unlock_spec_spec_instance recursive_mutex.lock_spec'_spec_instance recursive_mutex.unlock_spec'_spec_instance : typeclass_instances.

Context (RM_IOWN_ALT : HasOwn (iPropI _Σ) recursive_mutex.cmraR). Existing Instance RM_IOWN_ALT.

Definition selected_alt_ctor : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::recursive_mutex()" := ltac:(typeclasses eauto). Definition selected_alt_lock : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::lock()" := ltac:(typeclasses eauto). Definition selected_alt_unlock : SpecFor mutex_recursive_cpp.source "std::recursive_mutex::unlock()" := ltac:(typeclasses eauto).

Definition alt_protocol_spec : mpredI := specify {| info_name := "basic_lockable_alternative_oracle()"; info_type := tFunction "bool" [] |} (\post[Vbool true] emp). Theorem alt_protocol_oracle_ok : denoteModule mutex_recursive_cpp.source ⊢ ▷ recursive_mutex.ctor_spec' ∗ ▷ recursive_mutex.dtor_spec ∗ ▷ recursive_mutex.lock_spec_alt' ∗ ▷ recursive_mutex.unlock_spec_alt' -∗ alt_protocol_spec. Proof using LOCKED MOD RM_IOWN_ALT STD_THREADS _Σ thread_info Σ σ.
rewrite -recursive_mutex.lock_spec'_equiv_lock_spec_alt'.
rewrite -recursive_mutex.unlock_spec'_equiv_unlock_spec_alt'.
unfold alt_protocol_spec.
verify_spec.

go $usenamed=true.
wname [protected_value_addr |-> intR 1$m 3] "Hvalue".
iExists [tele], emp%I, ().
iSplitR. { done. }
iSplitR. { iPureIntro. intros a. apply emp_weakly_objective. }
iIntros "(%g & HR & Htoken & Hused & Hinv)".
iDestruct "Hinv" as "#Hinv".
wname [current_thread thr] "Hthread".
iMod (recursive_mutex.use_thread_acquirable (TT := [tele]) thr g ∅ emp%I with "[$Hthread $Hused]") as "[Hused Hacq]"; first set_solver.
go $usenamed=true.
wname [mutex_addr |-> recursive_mutex.R (recursive_mutex.lock_gname g) 1$m] "HR".
iDestruct "Htoken" as "[Htoken1 Htoken2]".
iExists (1$m)%cQp, ((1 / 2)%Qp). iFrame "HR Htoken1".
iIntros "(HR & Hgiven1 & %n & %Hstep & Hacq)".

go $usenamed=true.
iExists (1$m)%cQp, (recursive_mutex.Held n args), ((1 / 2)%Qp). iFrame "HR Htoken2".
go $usenamed=true.
iExists (1$m)%cQp, args. go $usenamed=true.
iExists (1$m)%cQp. iFrame.
iExists (1$m)%cQp, _, _.
go $usenamed=true.
wname [recursive_mutex.acquireable g thr (recursive_mutex.release (recursive_mutex.Held n args)) emp] "Hacq".
iEval (rewrite -b0) in "Hacq".
iFrame "Hacq".
wname [recursive_mutex.token (recursive_mutex.lock_gname g) (1 / 2)] "Htoken1".
iIntros "(HR & Htoken2 & Hacq)".
iCombine "Htoken1 Htoken2" as "Htoken".
iEval (rewrite -b) in "Hacq".
go $usenamed=true.
iExists (1$m)%cQp, (1%Qp). iFrame "HR Htoken".
iIntros "(HR & Hgiven & %nfinal & %Hstepfinal & Hacq)".
go $usenamed=true.
iExists (1$m)%cQp, args. go $usenamed=true.
iExists (1$c)%cQp. iFrame.

wname [p |-> boolR 1$m (bool_decide (((3 + 4) * 3 - 1)%Z = 20%Z))] "Hret".
iEval (simpl) in "Hret".
iExists (∅ ∪ {[thr]}). iFrame "Hused".
iNext.
wname [bi_forall] "Hpost".
iApply ("Hpost" $! p).
rewrite prim._at_tptsto_fuzzyR_Vbool_primR. iFrame "Hret".
Qed.
End derived_alt_selection.
Theorem recursive_depth_fragments_same_thread_exclusive
    (g : recursive_mutex.gname) (th : thread_idT) (n m : nat) :
  recursive_mutex.locked g th n ∗ recursive_mutex.locked g th m ⊢ False.
Proof.
  iIntros "[Hleft Hright]".
  iApply (recursive_mutex.locked_excl_same_thread g th n m).
  iFrame.
Qed.

End phase_b_final.

