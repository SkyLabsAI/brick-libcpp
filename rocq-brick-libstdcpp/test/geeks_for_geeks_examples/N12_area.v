Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N12_area_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition area_of_rectangle (side1 side2 : Z) := side1 * side2.
  Definition perimeter_of_rectangle (side1 side2 : Z) := 2 * (side1 + side2).
  Definition side1 := 5.
  Definition side2 := 6.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m str
  ).

  cpp.spec "areaRectangle(int, int)" from source inline.
  cpp.spec "perimeterRectangle(int, int)" from source inline.

  Lemma main_ok : verify[source] "main()".
  Proof.
  Admitted.
End with_cpp.
