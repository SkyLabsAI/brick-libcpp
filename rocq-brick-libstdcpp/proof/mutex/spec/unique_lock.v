Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

(* Specs for "unique_lock<std::mutex>".
TODO: to be replaced by generic specs + instantiations.
 *)
Module unique_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context `{HAS_THREADS : !HasStdThreads Σ}.

    (* a unique_lock may have an associated mutex, if so it holds
      (Some (b * mutex_state)) where b indicates whether the unique_lock
      has acquired the associated mutex. *)
    Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      cQp.t -> option (bool * (ptr * gname * Qp * mpred)) -> Rep.

    Definition owned (om : option (bool * (ptr * gname * Qp * mpred))) : bool :=
      match om with
      | Some (own, _) => own
      | None => false
      end.

    Definition mutex (om : option (bool * (ptr * gname * Qp * mpred))) : ptr :=
      match om with
      | Some (_, (mp, g, q, P)) => mp
      | None => nullptr
      end.

    #[only(cfracsplittable,type_ptr="std::unique_lock<std::mutex>")] derive R.

    #[global] Instance: LearnEqF1 R := ltac:(solve_learnable).

    (* TODO maybe a class / interface Lockable that exposes do_lock, do_unlock
      and the rep predicate R, formalizing the C++ lockable concept
      <https://en.cppreference.com/w/cpp/named_req/Lockable.html>.

      Instantiate with mutex, recursive_mutex, maybe in different styles (AC
      and invariant styles).
    *)

    Definition do_unlock (thr : thread_idT) (lk : ptr * gname * Qp * mpred) (Q : mpred) : mpred :=
      match lk with
      | (mp, g, q, P) =>
        mutex.locked g thr q ** ▷P **
        (* TODO readd *)
        (* ▷ *)
        (mutex.token g q -* Q)
      end.
    #[global] Arguments do_unlock /.

    Definition do_lock (thr : thread_idT) (lk : ptr * gname * Qp * mpred) (Q : mpred) : mpred :=
      match lk with
      | (mp, g, q, P) =>
        mutex.token g q **
        (* TODO readd *)
        (* ▷ *)
        (mutex.locked g thr q ** ▷P -* Q)
      end.
    #[global] Arguments do_lock /.

    cpp.spec "std::unique_lock<std::mutex>::unique_lock()"
      as default_ctor_spec from source with (
      \this this
      \post this |-> R 1$m None
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&)" as mutex_ctor_spec_alt from source with (
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{g q P} mp |-> mutex.R g q$m P
      \persist{thr} current_thread thr
      \pre{K} do_lock thr (mp, g, q, P) K
      \post
        this |-> R 1$m (Some (true, (mp, g, q, P))) **
        K
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&)" as mutex_ctor_spec from source with (
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{g q P} mp |-> mutex.R g q$m P
      \pre mutex.token g q
      \persist{thr} current_thread thr
      \post
        this |-> R 1$m (Some (true, (mp, g, q, P))) **
        P ** mutex.locked g thr q
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&, std::defer_lock_t)" as mutex_defer_ctor_spec from source with (
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{g q P} mp |-> mutex.R g q$m P
      \arg{def_p} "" (Vptr def_p)
      \post this |-> R 1$m (Some (false, (mp, g, q, P)))
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::unique_lock<std::mutex> &&)" as move_ctor_spec from source with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{om} other |-> R 1$m om
      \post
        this |-> R 1$m om **
        other |-> R 1$m None
    ).

    (** Ensures the associated mutex is unlocked and the ownership
    is returned to the continuation <Q>.
    XXX: creates more wands than we'd like and hinders client proofs. *)
    Definition ensure_unlock (thr : thread_idT) (om : option (bool * (ptr * gname * Qp * mpred))) (Q : mpred) : mpred :=
      match om with
      | Some (true, (mp, g, q, P)) =>
        letI* := do_unlock thr (mp, g, q, P) in
        (* ▷ *)
        mp |-> mutex.R g q$m P -* Q
      | Some (false, (mp, g, q, P)) =>
        (* ▷  *)
        (mp |-> mutex.R g q$m P -* Q)
      | _ =>
        (* ▷ *)
        Q
      end.
    #[global] Arguments ensure_unlock /.

    cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec from source with (
      \this this
      \persist{thr} current_thread thr
      \pre{om} this |-> R 1$m om
      \pre{K}
        ensure_unlock thr om K
      \post K).

    (** Duplicates [ensure_unlock], but proven equivalent and easier to apply, so
    comes after to be the default. *)
    cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec_alt from source with (
      \this this
      \persist{thr} current_thread thr
      \pre{om} this |-> R 1$m om
      \pre
        match om with
        | Some (true, (mp, g, q, P)) => mutex.locked g thr q ** ▷P
        | _ => emp
        end
      \post
        match om with
        | Some (true, (mp, g, q, P)) => mp |-> mutex.R g q$m P ** mutex.token g q
        | Some (false, (mp, g, q, P)) => mp |-> mutex.R g q$m P
        | None => emp
        end
      ).

    Lemma dtor_spec_alt_entails_dtor_spec : dtor_spec_alt -|- dtor_spec.
    Proof.
      iSplit; iApply specify_mono; work with br_erefl; repeat case_match; subst;
        try (exfalso; congruence);
        ework with br_erefl.
      wname [bi_wand] "W".
      iApply ("W" with "[$] [$]").
    Qed.

    (* unlock the associated mutex, if any, and set input as the associated mutex.
    Should be equivalent to move_assign_spec. *)
    cpp.spec "std::unique_lock<std::mutex>::operator=(std::unique_lock<std::mutex> &&)" as move_assign_spec from source with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{om1} this |-> R 1$m om1
      \pre{om2} other |-> R 1$m om2
      \persist{thr} current_thread thr
      \pre{K}
        ensure_unlock thr om1 K
      \post
        this |-> R 1$m om2 **
        other |-> R 1$m None **
        K
      ).

    Notation owns_lock_spec_body := (
      \this this
      \prepost{om q} this |-> R q om
      \post [Vbool (owned om)] emp) (only parsing).

    cpp.spec "std::unique_lock<std::mutex>::owns_lock() const" as owns_lock_spec
      from source with (owns_lock_spec_body).

    cpp.spec "std::unique_lock<std::mutex>::operator bool() const" as operator_bool_spec
      from source with (owns_lock_spec_body).

    cpp.spec "std::unique_lock<std::mutex>::mutex() const" as mutex_spec from source with (
      \this this
      \prepost{om q} this |-> R q om
      \post[Vptr (mutex om)] emp
    ).

    (* these preconditions statically rule out cases that throw exceptions, such as:
    - If there is no associated mutex, std::system_error with an error code of std::errc::operation_not_permitted.
    - If the mutex is already locked by this unique_lock (in other words, owns_lock() is true), std::system_error with an error code of std::errc::resource_deadlock_would_occur. *)
    cpp.spec "std::unique_lock<std::mutex>::lock()" as lock_spec from source with (
      \this this
      \pre{mp g q P} this |-> R 1$m (Some (false, (mp, g, q, P)))
      \pre mutex.token g q
      \persist{thr} current_thread thr
      \post
        this |-> R 1$m (Some (true, (mp, g, q, P))) **
        P ** mutex.locked g thr q).

    cpp.spec "std::unique_lock<std::mutex>::lock()" as lock_spec_alt from source with (
      \this this
      \pre{mm} this |-> R 1$m (Some (false, mm))
      \persist{thr} current_thread thr
      \pre{K} do_lock thr mm K
      \post
        this |-> R 1$m (Some (true, mm)) **
        K).

    cpp.spec "std::unique_lock<std::mutex>::unlock()" as unlock_spec from source with (
      \this this
      \pre{mp g q P} this |-> R 1$m (Some (true, (mp, g, q, P)))
      \persist{thr} current_thread thr
      \pre mutex.locked g thr q
      \pre ▷P
      \post
        this |-> R 1$m (Some (false, (mp, g, q, P))) **
        mutex.token g q
    ).

    cpp.spec "std::unique_lock<std::mutex>::unlock()" as unlock_spec_alt from source with (
      \this this
      \pre{mm} this |-> R 1$m (Some (true, mm))
      \persist{thr} current_thread thr
      \pre{K} do_unlock thr mm K
      \post
        this |-> R 1$m (Some (false, mm)) **
        K
    ).

    Lemma lock_spec_entails_lock_spec_alt : lock_spec |-- lock_spec_alt.
    Proof.
      apply specify_mono.
      go.
      (* XXX needs removing later in do_lock, or a stronger specify_mono offering a later. *)
      repeat case_match; go.
    Qed.

    Lemma unlock_spec_entails_unlock_spec_alt : unlock_spec |-- unlock_spec_alt.
    Proof.
      apply specify_mono.
      go.
      (* XXX needs removing later in do_unlock, or a stronger specify_mono offering a later. *)
      repeat case_match; go.
    Qed.

    Lemma lock_spec_alt_entails_lock_spec : lock_spec_alt |-- lock_spec.
    Proof.
      apply specify_mono.
      go.
      (* failed goal: ▷ P -∗ P. This might work with a stronger specify_mono offering a later. *)
      admit.
      all: fail.
    Abort.

    Lemma unlock_spec_alt_entails_unlock_spec : unlock_spec_alt |-- unlock_spec.
    Proof.
      apply specify_mono.
      go.
    Qed.

  End with_cpp.
End unique_lock.
