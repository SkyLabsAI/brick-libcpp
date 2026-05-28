Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.requirements.


Module unique_lock.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  Record M {T : Type} : Type :=
  { is_held : bool
  ; mutex_ptr : ptr
  ; mutex_q : Qp
  ; mutex_m : T }.
  #[global] Arguments M _ : clear implicits.
  #[only(lens)] derive M.

  (* a unique_lock may have an associated mutex, if so it holds
      (Some (b * mutex_state)) where b indicates whether the unique_lock
      has acquired the associated mutex. *)
  Parameter R : forall {σ : genv} ty {T} mutexR `{!BasicLockable ty (T:=T) mutexR},
    cQp.t -> option (M T) -> Rep.

  Definition owned {T} (om : option (M T)) : bool :=
    match om with
    | Some m => m.(is_held)
    | None => false
    end.

  Definition mutex {T} (om : option (M T)) : ptr :=
    match om with
    | Some m => m.(mutex_ptr)
    | None => nullptr
    end.

  #[global] Declare Instance R_cfrac {σ : genv} `{!BasicLockable ty (T:=T) mutexR} :
    CFractional1 mutexR ->
    CFractional1 (R ty mutexR).

  #[global] Instance R_as_cfrac {σ : genv} `{!BasicLockable ty (T:=T) mutexR} :
    CFractional1 mutexR ->
    AsCFractional1 (R ty mutexR).
  Proof. solve_as_cfrac. Qed.

  (* #[global] Declare Instance R_timeless {σ : genv} `{!BasicLockable ty (T:=T) mutexR} : *)
  (*   Timeless2 mutexR -> *)
  (*   Timeless2 (R ty mutexR). *)

  #[global] Declare Instance R_cfrac_valid {σ : genv} `{!BasicLockable ty (T:=T) mutexR} :
    CFracValid1 (R ty mutexR).

  #[global] Declare Instance R_type_ptr {σ : genv} `{!BasicLockable ty (T:=T) mutexR} q om :
    Typed ("std::unique_lock" .<< Atype ty >>) (R ty mutexR q om).

  Section with_threads.
    Context {σ : genv}.

    Context `{HAS_THREADS : !HasStdThreads Σ}.
    Context ty {mutexT} mutexR `{!BasicLockable ty (T:=mutexT) mutexR}.

    #[global] Instance: LearnEqF1 (R ty mutexR) := ltac:(solve_learnable).
    #[local] Notation R := (R ty (T:=mutexT) mutexR).

    (* TODO: all the following specs should be generalized over the lock type, except for [lock_spec] and [unlock_spec]. *)

    cpp.spec "std::unique_lock<std::mutex>::unique_lock()"
      as default_ctor_spec from source with (
      \this this
      \post this |-> R 1$m None
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&)" as mutex_ctor_spec_alt from source with (
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{q m} mp |-> mutexR q$m m
      \pre{K} do_lock mp m K
      \post
        this |-> R 1$m (Some {| is_held := true ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |}) **
        K
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&, std::defer_lock_t)" as mutex_defer_ctor_spec from source with (
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{q m} mp |-> mutexR q$m m
      \arg{def_p} "" (Vptr def_p)
      \post this |-> R 1$m (Some {| is_held := false ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |})
    ).

    cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::unique_lock<std::mutex> &&)" as move_ctor_spec from source with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{om} other |-> R 1$m om
      \post
        this |-> R 1$m om **
        other |-> R 1$m None
    ).

    (** Ensures the associated mutex is unlocked and released. *)
    Definition ensure_unlock (om : option (M mutexT)) (Q : mpred) : mpred :=
      match om with
      | Some {| is_held := is_held ; mutex_ptr := mp ; mutex_q := q ; mutex_m := m |} =>
        if is_held then
          letI* := do_unlock mp m in
          mp |-> mutexR q$m m -* Q
        else
          ▷ (mp |-> mutexR q$m m -* Q)
      | _ =>
      (* TODO should this be [bi_later Q]? *)
        Q
      end%I.

    (* spec for dtor written with do_unlock.
    Should be equivalent to dtor_spec. *)
    cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec_alt from source with (
      \this this
      \pre{om} this |-> R 1$m om
      \pre{K} ensure_unlock om K
      \post K
      ).

    cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec from source with (
      \this this
      \pre{om} this |-> R 1$m om
      \pre{K}
        match om with
        | Some m =>
            if m.(is_held) then do_unlock m.(mutex_ptr) m.(mutex_m) K
            else K
        | _ => K
        end
      \post K **
        match om with
        | Some m => m.(mutex_ptr) |-> mutexR m.(mutex_q)$m m.(mutex_m)
        | None => emp
        end
      ).

    (* unlock the associated mutex, if any, and set input as the associated mutex.
    Should be equivalent to move_assign_spec. *)
    cpp.spec "std::unique_lock<std::mutex>::operator=(std::unique_lock<std::mutex> &&)" as move_assign_spec_alt from source with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{om1} this |-> R 1$m om1
      \pre{om2} other |-> R 1$m om2
      \pre{K} ensure_unlock om1 K
      \post
        this |-> R 1$m om2 **
        other |-> R 1$m None **
        K
      ).

    cpp.spec "std::unique_lock<std::mutex>::operator=(std::unique_lock<std::mutex> &&)" as move_assign_spec from source with (
      \this this
      \arg{other} "" (Vptr other)
      \pre{om1} this |-> R 1$m om1
      \pre{om2} other |-> R 1$m om2
      \persist{thr} current_thread thr
      \pre{K}
        match om1 with
        | Some m =>
            if m.(is_held) then do_unlock m.(mutex_ptr) m.(mutex_m) K
            else K
        | _ => K
        end
      \post
        this |-> R 1$m om2 **
        other |-> R 1$m None **
        K **
        match om1 with
        | Some m => m.(mutex_ptr) |-> mutexR m.(mutex_q)$m m.(mutex_m)
        | None => emp
        end
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

    (* TODO: these specs seem mutex-specific. unlock_spec doesn't seem good for recursive mutexes. *)

    (* these preconditions statically rule out cases that throw exceptions, such as:
    - If there is no associated mutex, std::system_error with an error code of std::errc::operation_not_permitted.
    - If the mutex is already locked by this unique_lock (in other words, owns_lock() is true), std::system_error with an error code of std::errc::resource_deadlock_would_occur. *)
    cpp.spec "std::unique_lock<std::mutex>::lock()" as lock_spec from source with (
      \this this
      \pre{mm} this |-> R 1$m (Some mm)
      \require ~~ mm.(is_held)
      \pre{K} do_lock mm.(mutex_ptr) mm.(mutex_m) K
      \post
        this |-> R 1$m (Some (mm &: _is_held .= true)%lens) **
        K).

    cpp.spec "std::unique_lock<std::mutex>::unlock()" as unlock_spec from source with (
      \this this
      \pre{mm} this |-> R 1$m (Some mm)
      \require mm.(is_held)
      \pre{K} do_unlock mm.(mutex_ptr) mm.(mutex_m) K
      \post
        this |-> R 1$m (Some (mm &: _is_held .= false)%lens) **
        K
    ).

  End with_threads.
End with_cpp.
End unique_lock.
