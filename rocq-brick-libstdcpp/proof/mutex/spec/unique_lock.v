Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Module unique_lock.
Section with_cpp.
  Context `{Σ : cpp_logic}.

    (* Parameter gname : Set. *)
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

    (* #[only(type_ptr="std::unique_lock<std::mutex>")] derive R. *)

    Section with_threads.
      Context {σ : genv}.
      Context `{HAS_THREADS : !HasStdThreads Σ}.

      (* TODO maybe a class / interface Lockable that exposes do_lock, do_unlock
         and the rep predicate R, formalizing the C++ lockable concept
         <https://en.cppreference.com/w/cpp/named_req/Lockable.html>.

         Instantiate with mutex, recursive_mutex, maybe in different styles (AC
         and invariant styles).
      *)
      Definition do_unlock (thr : thread_idT) (lk : ptr * gname * Qp * mpred) (Q : mpred) : mpred :=
        match lk with
        | (mp, g, q, P) =>
          mutex.locked g thr q ** ▷P ** |> (mutex.token g q -* Q)
        end.

      Definition do_lock (thr : thread_idT) (lk : ptr * gname * Qp * mpred) (Q : mpred) : mpred :=
        match lk with
        | (mp, g, q, P) =>
          mutex.token g q ** |> (mutex.locked g thr q ** ▷P -* Q)
        end.

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

      cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec_alt from source with (
        \this this
        \persist{thr} current_thread thr
        \pre{om} this |-> R 1$m om
        \pre{K}
          match om with
          | Some (true, mm) => do_unlock thr mm K
          | Some (false, (mp, g, q, P)) =>
            |> (mp |-> mutex.R g q$m P -* K)
          | _ => K
          end
        \post K
        ).

      cpp.spec "std::unique_lock<std::mutex>::~unique_lock()" as dtor_spec from source with (
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

      cpp.spec "std::unique_lock<std::mutex>::operator=(std::unique_lock<std::mutex> &&)" as move_assign_spec from source with (
        \this this
        \arg{other} "" (Vptr other)
        \pre{om1} this |-> R 1$m om1
        \pre{om2} other |-> R 1$m om2
        \persist{thr} current_thread thr
        \pre
          match om1 with
          | Some (true, (mp, g, q, P)) => mutex.locked g thr q ** ▷P
          | _ => emp
          end
        \post
          this |-> R 1$m om2 **
          other |-> R 1$m None **
          match om1 with
          | Some (true, (mp, g, q, P)) => mp |-> mutex.R g q$m P ** mutex.token g q
          | Some (false, (mp, g, q, P)) => mp |-> mutex.R g q$m P
          | None => emp
          end
        ).

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
        \pre{mp g q P} this |-> R 1$m (Some (false, (mp, g, q, P)))
        \pre mutex.token g q
        \persist{thr} current_thread thr
        \post
          this |-> R 1$m (Some (true, (mp, g, q, P))) **
          P ** mutex.locked g thr q).
    End with_threads.
End with_cpp.
End unique_lock.
