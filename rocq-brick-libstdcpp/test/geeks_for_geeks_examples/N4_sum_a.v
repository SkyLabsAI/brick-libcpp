Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N4_sum_a_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m (str ++ Z_to_string 20)
  ).

  Lemma main_ok : verify[source] main_spec.
  Proof.
    verify_spec; go.

    wp_for (fun ρ =>
      \pre{i1} _local ρ "i" |-> intR 1$m i1
      \pre _local ρ "a" |-> intR 1$m (11 + i1)
      \require 0 <= i1 <= 9
      \post* _local ρ "i" |-> anyR "int" 1$m
      \post* _local ρ "a" |-> intR 1$m 20
      \post emp
    ).

    go.
    wp_if; go.
    wp_for (fun ρ => emp); go.
  Qed.
End with_cpp.
