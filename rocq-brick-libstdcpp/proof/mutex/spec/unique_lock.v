Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Module unique_lock.
Section with_cpp.
  Context `{Σ : cpp_logic}.

    (* Parameter gname : Set. *)
    Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      cQp.t -> option (ptr * gname * Qp * mpred * bool) -> Rep.

    (* #[only(type_ptr="std::unique_lock<std::mutex>")] derive R. *)

    Section with_threads.
      Context {σ : genv}.
      Context `{HAS_THREADS : !HasStdThreads Σ}.

      cpp.spec "std::unique_lock<std::mutex>::unique_lock()"
        as default_ctor_spec from source with (
        \this this
        \post this |-> R 1$m None
      ).

      cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&)" as mutex_ctor_spec from source with (
        \this this
        \arg{mp} "" (Vptr mp)
        \pre{g q P} mp |-> mutex.R g q$m P
        \pre mutex.token g q
        \persist{thr} current_thread thr
        \post
          this |-> R 1$m (Some (mp, g, q, P, true)) **
          P ** mutex.locked g thr q
      ).

      cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::mutex&, std::defer_lock_t)" as mutex_defer_ctor_spec from source with (
        \this this
        \arg{mp} "" (Vptr mp)
        \pre{g q P} mp |-> mutex.R g q$m P
        \arg{def_p} "" (Vptr def_p)
        \post this |-> R 1$m (Some (mp, g, q, P, false))
      ).

      cpp.spec "std::unique_lock<std::mutex>::unique_lock(std::unique_lock<std::mutex> &&)" as move_ctor_spec from source with (
        \this this
        \arg{other} "" (Vptr other)
        \pre{om} other |-> R 1$m om
        \post
          this |-> R 1$m om **
          other |-> R 1$m None
      ).

      cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec from source with (
        \this this
        \persist{thr} current_thread thr
        \pre{om} this |-> R 1$m om
        \pre
          match om with
          | Some (mp, g, q, P, true) => mutex.locked g thr q ** ▷P
          | _ => emp
          end
        \post
          match om with
          | Some (mp, g, q, P, true) => mp |-> mutex.R g q$m P ** mutex.token g q
          | Some (mp, g, q, P, false) => mp |-> mutex.R g q$m P
          | None => emp
          end
        ).

      cpp.spec "std::unique_lock<std::mutex>::operator=(std::unique_lock<std::mutex> &&)" as move_assign_spec from source with (
        \this this
        \arg{other} "" (Vptr other)
        \pre{om1} this |-> R 1$m om1
        \pre{om2} other |-> R 1$m om2
        \persist{thr} current_thread thr
        \pre
          match om1 with
          | Some (mp, g, q, P, true) => mutex.locked g thr q ** ▷P
          | _ => emp
          end
        \post
          this |-> R 1$m om2 **
          other |-> R 1$m None **
          match om1 with
          | Some (mp, g, q, P, true) => mp |-> mutex.R g q$m P ** mutex.token g q
          | Some (mp, g, q, P, false) => mp |-> mutex.R g q$m P
          | None => emp
          end
        ).

      Definition owned (om : option (ptr * gname * Qp * mpred * bool)) : bool :=
        match om with
        | Some (mp, g, q, P, own) => own
        | None => false
        end.

      Definition mutex (om : option (ptr * gname * Qp * mpred * bool)) : ptr :=
        match om with
        | Some (mp, g, q, P, own) => mp
        | None => nullptr
        end.

      cpp.spec "std::unique_lock<std::mutex>::owns_lock() const" as owns_lock_spec from source with (
        \this this
        \prepost{om q} this |-> R q om
        \post [Vbool (owned om)] emp).

      cpp.spec "std::unique_lock<std::mutex>::operator bool() const" as operator_bool_spec from source with (
        \this this
        \prepost{om q} this |-> R q om
        \post [Vbool (owned om)] emp).

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
        \pre{mp g q P} this |-> R 1$m (Some (mp, g, q, P, false))
        \pre mutex.token g q
        \persist{thr} current_thread thr
        \post
          this |-> R 1$m (Some (mp, g, q, P, true)) **
          P ** mutex.locked g thr q).
    End with_threads.
End with_cpp.
End unique_lock.
