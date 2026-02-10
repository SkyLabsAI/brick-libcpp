Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N0_hello_world_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" from N0_hello_world_cpp.source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m (str ++ "Hello World")).

  (* cpp.spec "puts" from source as puts_spec with (
    \arg{p} "" (Vptr p)
    \prepost{q s} p |-> cstring.R q s
    \post{n}[Vint n] emp). *)

  Lemma main_ok : verify?[source] main_spec.
  Proof.
    verify_spec; go.
  Qed.

End with_cpp.
