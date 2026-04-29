Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.

Module scoped_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (* Parameter gname : Set. *)
    Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      cQp.t -> list (ptr * gname * Qp * mpred) -> Rep.

    #[only(type_ptr="std::scoped_lock<std::mutex, std::mutex>")] derive R.
    #[only(cfractional,ascfractional,cfracvalid)] derive R.

    Section with_threads.
      Context {σ : genv}.
      Context `{HAS_THREADS : !HasStdThreads Σ}.

      #[global] Instance: LearnEqF1 R := ltac:(solve_learnable).

      cpp.spec
      "std::scoped_lock<...<std::mutex, std::mutex>>::scoped_lock(std::mutex&, std::mutex&)"
      (* "std::scoped_lock<std::mutex, std::mutex>::scoped_lock(std::mutex&, std::mutex&)" *)
      as ctor_spec from source with (
        \this this
        \arg{mp1} "" (Vptr mp1)
        \pre{g1 q1 P1} mp1 |-> mutex.R g1 q1$m P1
        \pre mutex.token g1 q1
        \arg{mp2} "" (Vptr mp2)
        \pre{g2 q2 P2} mp2 |-> mutex.R g2 q2$m P2
        \pre mutex.token g2 q2
        \persist{thr} current_thread thr
        \post
          this |-> R 1$m [ (mp1, g1, q1, P1); (mp2, g2, q2, P2)] **
          P1 ** mutex.locked g1 thr q1 **
          P2 ** mutex.locked g2 thr q2
      ).

      cpp.spec "std::scoped_lock<...<std::mutex, std::mutex>>::~scoped_lock()"
        as dtor_spec from source with (
        \this this
        \persist{thr} current_thread thr
        \pre{
          mp1 mp2
          g1 q1 P1
          g2 q2 P2
        }
          this |-> R 1$m [ (mp1, g1, q1, P1); (mp2, g2, q2, P2)]
        \pre |> P1
        \pre |> P2
        \pre mutex.locked g1 thr q1
        \pre mutex.locked g2 thr q2
        \post
          mp1 |-> mutex.R g1 q1$m P1 ** mutex.token g1 q1 **
          mp2 |-> mutex.R g2 q2$m P2 ** mutex.token g2 q2
      ).

      cpp.spec "foo()" as foo_spec from source with
      (
        \persist{thr} current_thread thr
        \post emp
      ).

      Lemma foo_ok : verify[source] foo_spec.
      Proof.
        verify_spec; go.
        iExists emp; go.
        iExists emp; go.
      Qed.
    End with_threads.
  End with_cpp.

End scoped_lock.
