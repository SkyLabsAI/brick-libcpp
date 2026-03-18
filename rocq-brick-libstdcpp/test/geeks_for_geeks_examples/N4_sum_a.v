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
    verify_spec.
    go.
    wp_for (fun ρ =>
      Exists x,
        _local ρ "a" |-> intR 1$m (11 + x) **
        _local ρ "b" |-> intR 1$m 9 **
        _local ρ "i" |-> intR 1$m x **
        [| 0 <= x <= 9 |])%I.
    go with pick_frac.
    wp_if.
    all: go with pick_frac.
    wp_for (fun ρ =>
      _local ρ "a" |-> intR 1$m 20 **
      _local ρ "b" |-> intR 1$m 9 **
      _local ρ "i" |-> intR 1$m 0)%I.
    go with pick_frac.
  Qed.
End with_cpp.
