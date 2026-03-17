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
    verify_shift.
    go.
    wp_for (fun rho =>
      Exists a i,
        _local rho "a" |-> intR 1$m a **
        _local rho "b" |-> intR 1$m 9 **
        _local rho "i" |-> intR 1$m i **
        [| a = 11 + i /\ 0 <= i <= 9 |])%Z.
    go.
    wp_if => Hi.
    all: go.
    wp_for (fun rho =>
      Exists a i,
        _local rho "a" |-> intR 1$m a **
        _local rho "b" |-> intR 1$m 9 **
        _local rho "i" |-> intR 1$m i **
        [| a = 20 /\ i = 0 |])%Z.
    go.
    iModIntro.
    go.
  Qed.
End with_cpp.
