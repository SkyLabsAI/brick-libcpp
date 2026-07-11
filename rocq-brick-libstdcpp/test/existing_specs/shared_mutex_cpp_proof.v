
Require Import skylabs.brick.libstdcpp.test.existing_specs.shared_mutex_try_oracles_cpp.

Require Import skylabs.brick.libstdcpp.test.existing_specs.shared_mutex_cpp.

Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex.
Require Import skylabs.brick.libstdcpp.cassert.spec.
(* Keep the shared user registry atomic for separation-logic automation. *)
#[global] Hint Opaque shared_mutex.used_threads : sl_opacity typeclass_instances.

Section binding_selection_evidence.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  (* These definitions freeze the actual typeclass-selected registration. *)
  Definition inferred_ctor_registration :
      SpecFor source "std::shared_mutex::shared_mutex()" :=
    ltac:(typeclasses eauto).
  Definition inferred_dtor_registration :
      SpecFor source "std::shared_mutex::~shared_mutex()" :=
    ltac:(typeclasses eauto).
  Definition inferred_lock_registration :
      SpecFor source "std::shared_mutex::lock()" :=
    ltac:(typeclasses eauto).
  Definition inferred_try_lock_registration :
      SpecFor source "std::shared_mutex::try_lock()" :=
    ltac:(typeclasses eauto).
  Definition inferred_unlock_registration :
      SpecFor source "std::shared_mutex::unlock()" :=
    ltac:(typeclasses eauto).
  Definition inferred_lock_shared_registration :
      SpecFor source "std::shared_mutex::lock_shared()" :=
    ltac:(typeclasses eauto).
  Definition inferred_try_lock_shared_registration :
      SpecFor source "std::shared_mutex::try_lock_shared()" :=
    ltac:(typeclasses eauto).
  Definition inferred_unlock_shared_registration :
      SpecFor source "std::shared_mutex::unlock_shared()" :=
    ltac:(typeclasses eauto).
End binding_selection_evidence.

Module alternative_registration_evidence.
  #[local] Remove Hints
    shared_mutex.lock_spec_spec_instance
    shared_mutex.try_lock_spec_spec_instance
    shared_mutex.unlock_spec_spec_instance
    : typeclass_instances.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
    Context `{!shared_mutex.lockedG Σ}.

    Definition inferred_alt_lock_registration :
        SpecFor source "std::shared_mutex::lock()" :=
      ltac:(typeclasses eauto).
    Definition inferred_alt_try_lock_registration :
        SpecFor source "std::shared_mutex::try_lock()" :=
      ltac:(typeclasses eauto).
    Definition inferred_alt_unlock_registration :
        SpecFor source "std::shared_mutex::unlock()" :=
      ltac:(typeclasses eauto).
  End with_cpp.
End alternative_registration_evidence.

Require Import skylabs.auto.cpp.prelude.test.

Require Import skylabs.brick.libstdcpp.test.existing_specs.shared_mutex_try_oracles_cpp.

Section primary_client_proofs.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  cpp.spec "lifecycle_scope()" as lifecycle_scope_spec
      from shared_mutex_cpp.source with (
    \post[Vint 17] emp).

  Lemma lifecycle_scope_ok :
    verify[shared_mutex_cpp.source] "lifecycle_scope()".
  Proof.

verify_spec; go $usenamed=true.

iExists (const emp); simpl; go $usenamed=true.

Qed.

End primary_client_proofs.

Section alternative_client_proofs.
  #[local] Remove Hints
    shared_mutex.lock_spec_spec_instance
    shared_mutex.try_lock_spec_spec_instance
    shared_mutex.unlock_spec_spec_instance
    : typeclass_instances.

  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  cpp.spec "exclusive_alt_cycle()" as exclusive_alt_cycle_spec
      from shared_mutex_cpp.source with (
    \persist{thr} current_thread thr
    \post[Vint 42] emp).

  Lemma exclusive_alt_cycle_ok :
    verify[shared_mutex_cpp.source] "exclusive_alt_cycle()".
  Proof.

verify_spec; go $usenamed=true.

iExists (const emp); simpl. iSplit; first work $usenamed=true.

iIntros "(%g & HR & Hused)". iMod (shared_mutex.login thr g empty with "Hused") as "[Hused Husers]"; first set_solver.

wuntil Kfree (go $usenamed=true).

wname [shared_mutex.users g {[thr]}] "Husers". rewrite /Kfree/=. iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]") as "Hused"; first set_solver.

go $usenamed=true.

Qed.

  cpp.spec "try_exclusive_alt_oracle()" as try_exclusive_alt_oracle_spec
      from shared_mutex_try_oracles_cpp.source with (
    \persist{thr} current_thread thr
    \post{result} [result] [| result = Vint 80 \/ result = Vint 81 |]).

  Lemma try_exclusive_alt_oracle_ok :
    verify[shared_mutex_try_oracles_cpp.source] "try_exclusive_alt_oracle()".
  Proof.

verify_spec; go $usenamed=true.

iExists (const emp); simpl. iSplit; first work $usenamed=true.

iIntros "(%g & HR & Hused)". iMod (shared_mutex.login thr g empty with "Hused") as "[Hused Husers]"; first set_solver.

wuntil Kfree (go $usenamed=true).

go $usenamed=true.

wp_if.

all: intros; subst _x_0.

all: wuntil Kfree (go $usenamed=true).

all: go $usenamed=true.

all: iExists t; iFrame.

all: iIntros "[HR Husers]".

all: iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]") as "Hused"; first set_solver.

all: go $usenamed=true.

1: iExists (Vint 81). 2: iExists (Vint 80).

all: go $usenamed=true.

all: iPureIntro; simpl; auto.

Qed.

End alternative_client_proofs.

Section canonical_client_proofs.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  cpp.spec "exclusive_canonical_cycle()" as exclusive_canonical_cycle_spec
      from shared_mutex_cpp.source with (
    \persist{thr} current_thread thr
    \post[Vint 52] emp).

  Lemma exclusive_canonical_cycle_ok :
    verify[shared_mutex_cpp.source] "exclusive_canonical_cycle()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (const emp); simpl. iSplit; first work $usenamed=true.
    iIntros "(%g & HR & Hused)".
    iMod (shared_mutex.login thr g empty with "Hused")
      as "[Hused Husers]"; first set_solver.
    wuntil Kfree (go $usenamed=true).
    wname [shared_mutex.users g {[thr]}] "Husers".
    rewrite /Kfree/=.
    iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]")
      as "Hused"; first set_solver.
    go $usenamed=true.
  Qed.

  cpp.spec "shared_cycle()" as shared_cycle_spec
      from shared_mutex_cpp.source with (
    \persist{thr} current_thread thr
    \post[Vint 60] emp).

  Lemma shared_cycle_ok :
    verify[shared_mutex_cpp.source] "shared_cycle()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (const emp); simpl. iSplit; first work $usenamed=true.
    iIntros "(%g & HR & Hused)".
    iMod (shared_mutex.login thr g empty with "Hused")
      as "[Hused Husers]"; first set_solver.
    wuntil Kfree (go $usenamed=true).
    iExists t; iFrame.
    iIntros "[HR Husers]".
    iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]")
      as "Hused"; first set_solver.
    go $usenamed=true.
  Qed.

  cpp.spec "exclusive_then_shared_cycle()" as exclusive_then_shared_cycle_spec
      from shared_mutex_cpp.source with (
    \persist{thr} current_thread thr
    \post[Vint 71] emp).

  Lemma exclusive_then_shared_cycle_ok :
    verify[shared_mutex_cpp.source] "exclusive_then_shared_cycle()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (const emp); simpl. iSplit; first work $usenamed=true.
    iIntros "(%g & HR & Hused)".
    iMod (shared_mutex.login thr g empty with "Hused")
      as "[Hused Husers]"; first set_solver.
    wuntil Kfree (go $usenamed=true).
    iExists t; iFrame.
    iIntros "[HR Husers]".
    iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]")
      as "Hused"; first set_solver.
    go $usenamed=true.
  Qed.

  cpp.spec "try_exclusive_canonical_oracle()" as try_exclusive_canonical_oracle_spec
      from shared_mutex_try_oracles_cpp.source with (
    \persist{thr} current_thread thr
    \post{result} [result] [| result = Vint 90 \/ result = Vint 91 |]).

  Lemma try_exclusive_canonical_oracle_ok :
    verify[shared_mutex_try_oracles_cpp.source]
      "try_exclusive_canonical_oracle()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (const emp); simpl. iSplit; first work $usenamed=true.
    iIntros "(%g & HR & Hused)".
    iMod (shared_mutex.login thr g empty with "Hused")
      as "[Hused Husers]"; first set_solver.
    wuntil Kfree (go $usenamed=true).
    wp_if.
    all: intros; subst.
    all: wuntil Kfree (go $usenamed=true).
    all: iExists t; iFrame.
    all: iIntros "[HR Husers]".
    all: iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]")
      as "Hused"; first set_solver.
    all: go $usenamed=true.
    1: iExists (Vint 91). 2: iExists (Vint 90).
    all: go $usenamed=true.
    all: iPureIntro; simpl; auto.
  Qed.

  cpp.spec "try_shared_oracle()" as try_shared_oracle_spec
      from shared_mutex_try_oracles_cpp.source with (
    \persist{thr} current_thread thr
    \post{result} [result]
      [| result = Vint (-1) \/ result = Vint 100 |]).

  Lemma try_shared_oracle_ok :
    verify[shared_mutex_try_oracles_cpp.source] "try_shared_oracle()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (const emp); simpl. iSplit; first work $usenamed=true.
    iIntros "(%g & HR & Hused)".
    iMod (shared_mutex.login thr g empty with "Hused")
      as "[Hused Husers]"; first set_solver.
    wuntil Kfree (go $usenamed=true).
    wp_if.
    all: intros; subst.

1: wuntil Kfree (go $usenamed=true).

1: iExists qP; iFrame.

1: iIntros "[HR Husers]".

all: wuntil Kfree (go $usenamed=true).

all: rewrite /Kfree /=.

all: work $usenamed=true.

all: iApply wp_destroy_val_intro.

all: iApply anyR_wp_destroy_prim_val; first done.

all: wname [result_addr |-> _] "Hresult".

all: iSplitL "Hresult"; first go $usenamed=true.

all: work $usenamed=true.

all: iApply wp_destroy_val_intro.

all: iApply anyR_wp_destroy_prim_val; first done.

all: wname [acquired_addr |-> _] "Hacquired".

all: iSplitL "Hacquired"; first go $usenamed=true.

all: work $usenamed=true.

all: iApply wp_destroy_val_intro.

all: iApply anyR_wp_destroy_prim_val; first done.

all: wname [protected_value_addr |-> _] "Hprotected".

all: iSplitL "Hprotected"; first go $usenamed=true.

all: wname [shared_mutex.users g {[thr]}] "Husers".

all: iMod (shared_mutex.logout thr g empty with "[$Hused $Husers]") as "Hused"; first set_solver.

all: go $usenamed=true.

1: iExists (Vint 100). 2: iExists (Vint (0 - 1)).

all: go $usenamed=true.

all: iPureIntro; simpl; auto.

Qed. End canonical_client_proofs.

Section negative_control.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.
  Context `{!shared_mutex.lockedG Σ}.

  Lemma duplicate_not_locked_impossible
      (g : shared_mutex.gname) (thr : thread_idT) :
    shared_mutex.users g {[thr]} ∗ shared_mutex.users g {[thr]} ⊢ False.
  Proof. apply shared_mutex.not_locked_unique. Qed.
End negative_control.

