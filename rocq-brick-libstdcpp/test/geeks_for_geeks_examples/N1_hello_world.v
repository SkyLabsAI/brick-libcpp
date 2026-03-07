Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N1_hello_world_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m (str ++ "Hello World")).

  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_spec; go.
  Qed.

End with_cpp.
