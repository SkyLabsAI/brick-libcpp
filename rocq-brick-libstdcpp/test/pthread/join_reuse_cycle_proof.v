(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Regression test for SkyLabsAI/brick-libcpp#262: join cycles through reused thread ids

    [pthread_join] used to require [pthread.handle γ this_thread tid P], where [this_thread] was
    the thread that created [tid], and promised to return 0. The spawner check was meant to rule
    out two threads joining each other. But [thread_idT] is the raw [pthread_t] value, which C
    libraries reuse once a thread is joined. As soon as a handle could move to another thread
    (by a [handle_local] hypothesis), [join_reuse_cycle.cpp] verified against [\post False],
    although it returns under a [pthread_join] that reports the resulting mutual join with
    [EDEADLK], which POSIX allows.

    [pthread.handle] no longer records a spawner, and [pthread_join] may now fail, losing the
    handle. Handles move between threads through the [pthread.handle_local_with] instance,
    which replaced that hypothesis. Every failure path of the program is reachable, and
    [test()] verifies against a postcondition it can meet. See [join_reuse_cycle.md]. *)

Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.brick.libstdcpp.thread.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.base_logic.lib.local_invariants.
Require Import skylabs.brick.libstdcpp.test.pthread.join_reuse_cycle_cpp.
Require Import skylabs.auto.cpp.prelude.proof.

Import thread_id_specs.

Section with_cpp.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MOD : !join_reuse_cycle_cpp.source ⊧ σ}.

  (** Keep auto's [UNSOUND_*] evaluation-order axioms out of the derivation: drop the hints
      that are, or whose proofs use, them. Evaluation orders are split with [nd_case]. *)
  Remove Hints eval.UNSOUND_eval_nd_B eval.UNSOUND_eval_l_nd_B eval.UNSOUND_nd_seq_B
    skylabs.auto.cpp.vc_rw.VcRwDefs.wp_operand_binop_wp_B
    skylabs.auto.cpp.hints.wp_path.wp_path_and.wp_lval_assign_B
    skylabs.auto.cpp.hints.wp_path.WpPrimRSep.wp_lval_assign_B
    : db_skylabs_wp.
  #[local] Transparent eval.

  Ltac nd_case :=
    match goal with
    | H : _ = ?pre ++ _ :: _ |- _ =>
        destruct pre as [|?[|?[|?[|? ?]]]]; simplify_eq/=;
        try (match goal with
             | H0 : [] = ?l ++ _ :: _ |- _ => destruct l; simplify_eq
             end)
    end.
  (** [go], splitting every nondeterministic evaluation order it reaches. *)
  Ltac gond := go; repeat (nd_case; try rewrite /wp.WPE.Mret /=; try go).

  Definition N : namespace := nroot .@ "join_reuse_cycle".

  (** What [test()] publishes: S's handle for X, X's id, and S's id. *)
  Definition Hx (sh : ptr) : mpred :=
    ∃ th γ tx,
      pthread.handle γ tx emp **
      sh ,, _field "Shared::x" |-> pthread.R 1$m tx **
      sh ,, _field "Shared::id0" |-> thread_idR 1$m th.

  #[local] Hint Opaque Hx : sl_opacity.

  (** [Shared::st] holds the published handle while it is nonzero. [Shared::failed] is set
      after a failed join. *)
  Definition I (sh : ptr) : mpred :=
    (∃ v : Z, sh ,, _field "Shared::st" |-> intR 1$m v **
       (if bool_decide (v = 0) then emp else Hx sh)) **
    (∃ f : Z, sh ,, _field "Shared::failed" |-> intR 1$m f).

  Abbreviation REFS sh fld :=
    (reference_to "Shared" sh ** reference_to "int" (sh ,, _field fld))%I (only parsing).

  cpp.spec "take_st(Shared*)" as take_st_spec with
    (\arg{sh} "sh" (Vptr sh)
     \persist inv N (I sh)
     \persist REFS sh "Shared::st"
     \post{v}[Vint v] if bool_decide (v = 0) then emp else Hx sh).

  cpp.spec "publish(Shared*)" as publish_spec with
    (\arg{sh} "sh" (Vptr sh)
     \persist inv N (I sh)
     \persist REFS sh "Shared::st"
     \pre Hx sh
     \post emp).

  cpp.spec "load_failed(Shared*)" as load_failed_spec with
    (\arg{sh} "sh" (Vptr sh)
     \persist inv N (I sh)
     \persist REFS sh "Shared::failed"
     \post{v}[Vint v] emp).

  cpp.spec "set_failed(Shared*)" as set_failed_spec with
    (\arg{sh} "sh" (Vptr sh)
     \persist inv N (I sh)
     \persist REFS sh "Shared::failed"
     \post emp).

  Lemma take_st_ok : verify[join_reuse_cycle_cpp.source] take_st_spec.
  Proof.
    verify_spec; gond.
    all: iApply wp_atom_exchange_n_cst; iSplit; [done|]; iSplit; [go|];
      rewrite /wrap_shift; iExists (⊤ ∖ ↑N);
      iInv N as "[(%v & >Hst & Hrest) Hf]" "Hclose";
      iModIntro; iNext; iExists (Vint v); iFrame "Hst";
      iIntros "Hst"; iMod ("Hclose" with "[Hst Hf]") as "_";
      [iNext; iFrame "Hf"; iExists 0; iFrame "Hst"; by rewrite bool_decide_true
      | iModIntro; go; iExact "Hrest"].
  Qed.

  Lemma publish_ok : verify[join_reuse_cycle_cpp.source] publish_spec.
  Proof.
    verify_spec; gond.
    all: iDestruct select (Hx _) as "Hx";
      iApply wp_atom_store_cst; iSplit; [done|]; iSplit; [go|];
      rewrite /wrap_shift; iExists (⊤ ∖ ↑N);
      iInv N as "[(%v & >Hst & _) Hf]" "Hclose";
      iModIntro; iNext; iSplitL "Hst"; [rewrite -primR_anyR; iFrame "Hst"|];
      iIntros "Hst"; iMod ("Hclose" with "[Hst Hx Hf]") as "_";
      [iNext; iFrame "Hf"; iExists 1; iFrame "Hst"; by rewrite bool_decide_false
      | iModIntro; go].
  Qed.

  Lemma load_failed_ok : verify[join_reuse_cycle_cpp.source] load_failed_spec.
  Proof.
    verify_spec; gond.
    all: iApply wp_atom_load_cst; iSplit; [done|];
      rewrite /wrap_shift; iExists (⊤ ∖ ↑N);
      iInv N as "[Hst (%f & >Hf)]" "Hclose";
      iModIntro; iNext; iExists (Vint f), (1$m)%cQp; iFrame "Hf";
      iIntros "Hf"; iMod ("Hclose" with "[Hst Hf]") as "_";
      [iNext; iFrame | iModIntro; go].
  Qed.

  Lemma set_failed_ok : verify[join_reuse_cycle_cpp.source] set_failed_spec.
  Proof.
    verify_spec; gond.
    all: iApply wp_atom_store_cst; iSplit; [done|]; iSplit; [go|];
      rewrite /wrap_shift; iExists (⊤ ∖ ↑N);
      iInv N as "[Hst (%f & >Hf)]" "Hclose";
      iModIntro; iNext; iSplitL "Hf"; [rewrite -primR_anyR; iFrame "Hf"|];
      iIntros "Hf"; iMod ("Hclose" with "[Hst Hf]") as "_";
      [iNext; iFrame | iModIntro; go].
  Qed.

  (** ** Thread-local facts *)

  (** [reference_to] has no [LocalWith procTI] instance, so threads receive the facts it is
      built from, and rebuild it with [reference_to_intro]. *)
  Definition refL (ty : type) (p : ptr) : mpred :=
    strict_valid_ptr p ** has_type (Vptr p) (Tptr ty).

  #[local] Hint Opaque refL : sl_opacity.
  #[local] Instance refL_persistent ty p : Persistent (refL ty p).
  Proof. rewrite /refL. apply _. Qed.

  Lemma refL_reference_to ty p : refL ty p |-- reference_to ty p.
  Proof. rewrite /refL. iIntros "[V T]". iApply (reference_to_intro with "V T"). Qed.

  Lemma reference_to_refL ty p :
    zero_sized_array ty = false -> reference_to ty p |-- refL ty p.
  Proof.
    intros Hz. rewrite /refL reference_to_elim Hz has_type_ptr'.
    iIntros "(% & _ & #V & #S)". iFrame "#". done.
  Qed.

  Ltac use_refL :=
    repeat (iDestruct select (refL _ _) as "#R";
            iDestruct (refL_reference_to with "R") as "#?";
            iEval (rewrite /refL) in "R"; iDestruct "R" as "[#? #?]").

  #[local] Instance inv_local_with (P : mpred) : LocalWith procTI P -> LocalWith procTI (inv N P).
  Proof. intros. rewrite inv_eq /inv_def. apply _. Qed.

  #[local] Instance only_provable_local_with φ : LocalWith procTI ([| φ |] : mpred).
  Proof. rewrite only_provable.unlock. apply _. Qed.

  #[local] Instance thread_idR_local_with q th : LocalWithR procTI (thread_idR q th).
  Proof. rewrite thread_idR.unlock. apply _. Qed.

  #[local] Instance pthread_R_local_with q th : LocalWithR procTI (pthread.R q th).
  Proof. rewrite pthread.R.unlock. apply _. Qed.

  #[local] Instance Hx_local_with sh : LocalWith procTI (Hx sh).
  Proof. rewrite /Hx. apply _. Qed.

  #[local] Instance if_local_with (b : bool) (P Q : mpred) :
    LocalWith procTI P -> LocalWith procTI Q -> LocalWith procTI (if b then P else Q).
  Proof. by destruct b. Qed.

  #[local] Instance I_local_with sh : LocalWith procTI (I sh).
  Proof. rewrite /I. apply _. Qed.

  #[local] Instance refL_local_with ty p : LocalWith procTI (refL ty p).
  Proof. rewrite /refL. apply _. Qed.

  (** Process-local invariants ([local_invariants.inv_alloc]) only need this. *)
  #[local] Instance local_with_weakly_local_with (P : mpred) :
    LocalWith procTI P -> WeaklyLocalWith procTI P.
  Proof.
    intros HL j i1 i2 _. rewrite !monPred_at_exactly_at.
    apply HL. by rewrite !mlens_get_set.
  Qed.

  (** ** Thread functions *)

  #[local] Abbreviation PreY :=
    (fun (p : ptr) (_ : tele_arg [tele]) =>
       inv N (I p) ** Hx p ** refL "Shared" p **
       refL "int" (p ,, _field "Shared::failed")) (only parsing).
  #[local] Abbreviation PreX :=
    (fun (p : ptr) (_ : tele_arg [tele]) =>
       inv N (I p) ** refL "Shared" p ** refL "int" (p ,, _field "Shared::st") **
       refL "int" (p ,, _field "Shared::failed")) (only parsing).
  #[local] Abbreviation PreS :=
    (fun (p : ptr) (_ : tele_arg [tele]) =>
       inv N (I p) ** refL "Shared" p ** refL "int" (p ,, _field "Shared::st") **
       refL "int" (p ,, _field "Shared::failed") **
       p ,, _field "Shared::id0" |-> thread_idR 1$m default_thread_id **
       p ,, _field "Shared::x" |-> uninitR "unsigned long" 1$m) (only parsing).
  #[local] Abbreviation PostE :=
    (fun (p : ptr) (_ : tele_arg [tele]) (_ : thread_idT) => emp%I : mpred) (only parsing).
  #[local] Abbreviation PostS :=
    (fun (p : ptr) (_ : tele_arg [tele]) (_ : thread_idT) => Hx p) (only parsing).

  cpp.spec "y_fn(void*)" as y_spec with (pthread.starter_spec [tele] PreY PostE).
  cpp.spec "x_fn(void*)" as x_spec with (pthread.starter_spec [tele] PreX PostE).
  cpp.spec "s_fn(void*)" as s_spec with (pthread.starter_spec [tele] PreS PostS).

  (** [test()] can return: the threads keep using [sh] through the invariant. *)
  cpp.spec "test(Shared*)" as test_spec with
    (\arg{sh} "sh" (Vptr sh)
     \pre sh |-> structR "Shared" 1$m **
          sh ,, _field "Shared::st" |-> intR 1$m 0 **
          sh ,, _field "Shared::failed" |-> intR 1$m 0 **
          sh ,, _field "Shared::id0" |-> thread_idR 1$m default_thread_id **
          sh ,, _field "Shared::x" |-> uninitR "unsigned long" 1$m
     \post emp).

  Lemma y_starter : y_spec |-- _global "y_fn(void*)" |-> pthread.starter_specR [tele] PreY PostE.
  Proof. rewrite pthread.starter_specR.unlock. iIntros "H". iExact "H". Qed.
  Lemma x_starter : x_spec |-- _global "x_fn(void*)" |-> pthread.starter_specR [tele] PreX PostE.
  Proof. rewrite pthread.starter_specR.unlock. iIntros "H". iExact "H". Qed.
  Lemma s_starter : s_spec |-- _global "s_fn(void*)" |-> pthread.starter_specR [tele] PreS PostS.
  Proof. rewrite pthread.starter_specR.unlock. iIntros "H". iExact "H". Qed.

  (** Y: if its id is S's (reused) id, it joins X with the handle S created. The join may
      fail, and then Y sets [Shared::failed]. *)
  Lemma y_ok : verify[join_reuse_cycle_cpp.source] y_spec.
  Proof using MOD.
    verify_spec. gond. all: use_refL.
    all: iDestruct select (Hx _) as (th γ tx) "(? & ? & ?)".
    all: gond.
    all: case_bool_decide; gond.
    all: case_bool_decide; gond.
  Qed.

  (** X: takes S's handle for X, hands it to Y through Y's [Pre], and joins Y. *)
  Lemma x_ok : verify[join_reuse_cycle_cpp.source] x_spec.
  Proof using MOD.
    verify_spec. gond. all: use_refL.
    all: iDestruct select y_spec as "#Ys"; iDestruct (y_starter with "Ys") as "#?".
    all: gond.
    all: wp_while (fun _ => \post Hx argp).
    all: gond.
    all: case_bool_decide; gond.
    all: iExists _, PreY, PostE, arg; rewrite /refL; gond.
    all: case_bool_decide; gond.
    all: case_bool_decide; gond.
  Qed.

  (** S: records its id and creates X, then returns its handle for X through its [Post]. *)
  Lemma s_ok : verify[join_reuse_cycle_cpp.source] s_spec.
  Proof using MOD.
    verify_spec. gond. all: use_refL.
    all: iDestruct select x_spec as "#Xs"; iDestruct (x_starter with "Xs") as "#?".
    all: gond.
    all: iExists _, PreX, PostE, arg; rewrite /refL; gond.
    all: case_bool_decide; gond.
    all: rewrite /Hx; iExists _, _, _; iFrame.
  Qed.

  Ltac alloc_inv sh :=
    iDestruct select (sh ,, _field "Shared::st" |-> _)%I as "Hst";
    iDestruct select (sh ,, _field "Shared::failed" |-> _)%I as "Hf";
    iDestruct (observe (reference_to "int" _) with "Hst") as "#Rst";
    iDestruct (observe (reference_to "int" _) with "Hf") as "#Rf";
    iAssert (reference_to "Shared" sh) as "#Rsh"; [go|];
    iDestruct (reference_to_refL "int" (sh ,, _field "Shared::st") eq_refl with "Rst") as "#?";
    iDestruct (reference_to_refL "int" (sh ,, _field "Shared::failed") eq_refl with "Rf") as "#?";
    iDestruct (reference_to_refL "Shared" sh eq_refl with "Rsh") as "#?";
    iMod (local_invariants.inv_alloc procTI N ⊤ (I sh) with "[Hst Hf]") as "#?";
    [iNext; iSplitL "Hst"; [iExists 0; iFrame "Hst" | iExists 0; iFrame "Hf"] |].

  Lemma test_ok : verify[join_reuse_cycle_cpp.source] test_spec.
  Proof using MOD.
    verify_spec. alloc_inv sh.
    iDestruct select s_spec as "#Ss". iDestruct (s_starter with "Ss") as "#?".
    gond.
    all: iExists _, PreS, PostS; iExists skylabs.auto.telescopes.taO; gond.
    all: repeat (case_bool_decide; gond).
    all: wp_while (fun _ => \post emp); gond.
    all: case_bool_decide; gond.
  Qed.

  (** The whole program, from the C++ library specs it uses. *)
  Theorem test_from_specs :
    denoteModule join_reuse_cycle_cpp.source **
    pthread.create_spec ** pthread.join_spec ** abort_spec **
    get_id_spec ** thread_id_copy_ctor_spec ** thread_id_dtor_spec **
    thread_id_eq_spec ** thread_id_move_assign_spec
    |-- test_spec.
  Proof using MOD.
    iIntros "(#M & #C & #J & #A & #G & #CC & #D & #E & #MA)".
    iAssert take_st_spec as "#T". { iApply (take_st_ok with "M"). }
    iAssert publish_spec as "#P". { iApply (publish_ok with "M"). }
    iAssert load_failed_spec as "#L". { iApply (load_failed_ok with "M"). }
    iAssert set_failed_spec as "#F". { iApply (set_failed_ok with "M"). }
    iAssert y_spec as "#Y". { iApply (y_ok with "M"); iFrame "#". }
    iAssert x_spec as "#X". { iApply (x_ok with "M"); iFrame "#". }
    iAssert s_spec as "#S". { iApply (s_ok with "M"); iFrame "#". }
    iApply (test_ok with "M"); iFrame "#".
  Qed.

End with_cpp.
