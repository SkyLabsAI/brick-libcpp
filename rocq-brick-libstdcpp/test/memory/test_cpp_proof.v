Require Import skylabs.auto.cpp.prelude.proof.

Require Import skylabs.brick.libstdcpp.memory.spec.addressof.
Require Import skylabs.brick.libstdcpp.lib.tactics.
Require Import skylabs.brick.libstdcpp.test.memory.test_cpp.

NES.Begin memory.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    Lemma addressof_ok : __addressof_spec "C" source |-- verify?[source] "std::addressof<C>(C&)".
    Proof.
      verify_spec; go.
    Qed.

    Lemma __addressof_ok : verify?[source] "std::__addressof<C>(C&)".
    Proof.
      verify_spec; go.
    Abort.
  End with_cpp.
NES.End memory.
