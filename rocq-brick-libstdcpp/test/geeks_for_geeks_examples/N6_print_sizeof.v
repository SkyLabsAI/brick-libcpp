Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N6_print_sizeof_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition newline := "
"%bs.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m
        (str ++
        "Size of int is: " ++ Z_to_string 4 ++ newline ++
        "Size of char is: " ++ Z_to_string 1 ++ newline ++
        "Size of float is: " ++ Z_to_string 4 ++ newline ++
        "Size of double is: " ++ Z_to_string 8 ++ newline)
  ).

  Lemma main_ok : verify[source] "main()".
  Proof.
  Admitted.
End with_cpp.
