
Require Import skylabs.brick.libstdcpp.thread.defs.
(* Require Import skylabs.brick.libstdcpp.thread.reference_wrapper. *)
Require Import skylabs.brick.libstdcpp.thread.fptr.
Require Import skylabs.brick.libstdcpp.thread.spec.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

Require Import skylabs.brick.libstdcpp.thread.prelude.
Require Import skylabs.brick.libstdcpp.thread.test_cpp.

Module D.

  cpp.class "D" prefix "" from test_cpp.source
    dataclass { default_specs }.

End D.

(* Search primR HLearn. *)
(* Print Hint HLearn. *)

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!test_cpp.source ⊧ σ}.

  cpp.spec "main()" as main_spec with
      ( \post[Vint 0] emp ).
  cpp.spec "test1()" as test1_spec with
      ( \post emp ).
  cpp.spec "test2()" as test2_spec with
      ( \post emp ).

  cpp.spec "thread_1(int&)" as thread_1_spec
      with (
        \arg{x1} "x1" (Vref x1)
        \pre{a} x1 |-> intR 1$m a
        \post* x1 |-> intR 1$m (a + 1)
        \post emp ).

  cpp.spec "thread_2(int)" as thread_2_spec
      with (
        \arg{x2} "x1" (Vint x2)
        \post emp ).

  cpp.spec "thread_3(int*)" as thread_3_spec
      with (
        \arg{x3} "x1" (Vptr x3)
        \pre{a} x3 |-> intR 1$m a
        \post* x3 |-> intR 1$m (a + 2)
        \post emp ).

  cpp.spec "thread_4(int&&)" as thread_4_spec
      with (
        \arg{x4} "x1" (Vref x4)
        \prepost{q c} x4 |-> intR q c
        \post emp ).

  cpp.spec "thread_5(D)" as thread_5_spec
      with (
        \arg{x5} "x1" (Vptr x5)
        \prepost{q x} x5 |-> D.R q x
        \post emp ).

  cpp.spec "thread_6(D const &)" as thread_6_spec
      with (
        \arg{x5} "x1" (Vptr x5)
        \prepost{q x} x5 |-> D.R q x
        \post emp ).

  cpp.spec "thread_7(D const *)" as thread_7_spec
      with (
        \arg{x5} "x1" (Vptr x5)
        \prepost{q x} x5 |-> D.R q x
        \post emp ).

  (* very slow *)
  cpp.spec "thread_n(int&, int, int*, int&&, D, D&, const D &, D&&, D*, D const * )"
      as thread_n_spec default.
      (* with ( *)
      (*   \arg{x1} "x1" (Vref x1) *)
      (*   \arg{x2} "x1" (Vint x2) *)
      (*   \arg{x3} "x1" (Vptr x3) *)
      (*   \arg{x4} "x1" (Vref x4) *)
      (*   \arg{x5} "x1" (Vptr x5) *)
      (*   \arg{x5} "x1" (Vptr x5) *)
      (*   \arg{x5} "x1" (Vptr x5) *)
      (*   \prepost{q c} x4 |-> intR q c *)
      (*   \prepost{q d} x5 |-> D.R q d *)
      (*   \pre{a} x1 |-> intR 1$m a *)
      (*   \pre{b} x3 |-> intR 1$m b *)
      (*   \post* x1 |-> intR 1$m b *)
      (*   \post* x3 |-> intR 1$m a *)
      (*   \post emp *)
      (* ). *)

  (* utility for debugging *)
  Ltac wp_invoke_ctor :=
    lazymatch goal with
    | |- environments.envs_entails _ ?P =>
        eassert (X : CancelX _ [(□ ctor_spec _ _ _ _)%I] [tele] _ [P]);
        idtac
    end.

  Hint Opaque spec_internal : sl_opacity.

  #[program]
  Definition instantiate_refl_B {PROP} :=
    \bwd
    \proving{A X x} @instantiate.Instantiate.Instantiate.Instantiate _ A X x (x :> A)
    \end@{PROP}.
  Admit Obligations.

  #[program]
  Definition pure_refl_B {PROP} :=
    \bwd
    \proving{A x} [| x = (x :> A) |]
    \end@{PROP}.
  Admit Obligations.

  #[local] Hint Resolve pure_refl_B instantiate_refl_B : db_skylabs_syntactic.

  (* Search Bwd ([| _ = _ |]). *)

  Lemma test1_ok : verify?[source] test1_spec.
  Proof.

    verify_spec.
    go.

    Import precondition_of_hints.

    work.


    (*
For argument n, generated precondition features too much indirection


Goal:
  _ : n1_addr |-> intR 1$m 0
  --------------------------------------∗
  ∃ (x1 : ptr) (a0 : Z), x1 |-> intR 1$m a0 ∗ n1_addr |-> refR<"int"> 1$m x1 ∗ False ∗
    ∀ x : ptr,
      _p_ |-> refR<"void(int&)"> 1$m (_global "thread_1(int&)") ∗ x |-> primR "void" 1$m Vvoid ∗
     *)

  Abort.

  Lemma test2_ok : verify?[source] test1_spec.
  Proof. Abort.
  Lemma main_ok : verify?[source] test1_spec.
  Proof. Abort.

End with_cpp.
