(* Copyright (c) 2026 SkyLabs AI, Inc.
   Distributed under the BSD 3-Clause license; see LICENSE. *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.mutex.spec.scoped_lock.

(** A contract-level counterexample, paired with the native C++ witness.
    The model isolates the flag [lock_calls > 0]: [lock()] sets it, whereas
    [try_lock()] leaves it alone. It does not verify the underlying mutex
    or claim a linked C++ proof of [False]. *)
Section counterexample.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition counting_ty : type := "CountingMutex"%cpp_type.
  Definition counting_R (q : cQp.t) (_ : ptr) : Rep :=
    structR "CountingMutex" q.
  Definition called (flag : ptr) (b : bool) : mpred :=
    flag |-> primR Tbool 1$m (Vbool b).

  #[local] Instance counting_basic_lockable :
      BasicLockable counting_ty counting_R :=
    {| do_lock := fun _ flag K => called flag false ** (called flag true -* K)
     ; do_unlock := fun _ _ K => K |}.
  #[local] Instance counting_lockable : Lockable counting_ty counting_R :=
    {| do_try_lock := fun _ _ K => (∀ b : bool, K b)%I |}.

  (** Merely registering Lockable imposes no relation between these effects.
      Two false flags supply the ctor's do_lock premises with true flags
      as continuations. *)
  Lemma supplies_lock_effect this flag :
    called flag false |--
      do_lock counting_ty this flag (called flag true).
  Proof. cbn. iIntros "$". iIntros "$". Qed.

  Lemma try_lock_can_preserve_false this flag :
    called flag false |--
      do_try_lock counting_ty this flag (fun _ => called flag false).
  Proof. cbn. iIntros "H" (b). iExact "H". Qed.

  (** Check the existing exported ctor_spec, rather than introduce an
      assumed scoped_lock spec. It returns K1 and K2 although try_lock
      need not establish either lock-specific effect. A repair must
      revisit this diagnostic test. *)
  Lemma current_ctor_contract :
    scoped_lock.ctor_spec counting_ty counting_ty
      (mutexR1 := counting_R) (mutexR2 := counting_R) =
    specify.template.ctor
      ("std::scoped_lock" .<< Apack [Atype counting_ty; Atype counting_ty] >>)
      [Tref counting_ty; Tref counting_ty] $
      \this this
      \arg{mp1} "" (Vptr mp1)
      \pre{q1 flag1} mp1 |-> counting_R q1$m flag1
      \pre{K1} called flag1 false ** (called flag1 true -* K1)
      \arg{mp2} "" (Vptr mp2)
      \pre{q2 flag2} mp2 |-> counting_R q2$m flag2
      \pre{K2} called flag2 false ** (called flag2 true -* K2)
      \post this |-> scoped_lock.R counting_ty counting_ty counting_R counting_R
        1$m (scoped_lock.Mk mp1 q1 flag1, scoped_lock.Mk mp2 q2 flag2) ** K1 ** K2.
  Proof. reflexivity. Qed.

  Lemma ctor_promises_both_lock_effects :
    scoped_lock.ctor_spec counting_ty counting_ty
      (mutexR1 := counting_R) (mutexR2 := counting_R) |--
    specify.template.ctor
      ("std::scoped_lock" .<< Apack [Atype counting_ty; Atype counting_ty] >>)
      [Tref counting_ty; Tref counting_ty] $
      \this this
      \arg{mp1} "" (Vptr mp1)
      \pre{q1 flag1} mp1 |-> counting_R q1$m flag1
      \pre called flag1 false
      \arg{mp2} "" (Vptr mp2)
      \pre{q2 flag2} mp2 |-> counting_R q2$m flag2
      \pre called flag2 false
      \post this |-> scoped_lock.R counting_ty counting_ty counting_R counting_R
        1$m (scoped_lock.Mk mp1 q1 flag1, scoped_lock.Mk mp2 q2 flag2) **
        called flag1 true ** called flag2 true.
  Proof.
    rewrite current_ctor_contract /specify.template.ctor /specify.exact.ctor.
    apply specify_mono. intros this args post. cbn.
    iIntros "H".
    iDestruct "H" as (mp1 q1 flag1 mp2 q2 flag2)
      "(%Hargs & R1 & F1 & R2 & F2 & Hpost)".
    iExists mp1, q1, flag1, (called flag1 true),
      mp2, q2, flag2, (called flag2 true).
    iFrame "R1 R2 Hpost". iSplit; first done.
    iSplitL "F1".
    - iApply (supplies_lock_effect mp1 flag1). iExact "F1".
    - iApply (supplies_lock_effect mp2 flag2). iExact "F2".
  Qed.

  (** A legal lock/try_lock trace leaves one flag false, inconsistent
      with the corresponding true flag promised by the constructor.
      The two half permissions add to one, so disagreement of the values,
      rather than overfull ownership, causes the contradiction. *)
  Lemma false_flag_contradicts_promised_effect (flag : ptr) :
    flag |-> primR Tbool (1 / 2)$m (Vbool false) **
    flag |-> primR Tbool (1 / 2)$m (Vbool true) |-- False.
  Proof.
    iIntros "[Hfalse Htrue]".
    iDestruct (observe_2 [| Vbool false = Vbool true |]
      with "Hfalse Htrue") as %[=].
  Qed.
End counterexample.
