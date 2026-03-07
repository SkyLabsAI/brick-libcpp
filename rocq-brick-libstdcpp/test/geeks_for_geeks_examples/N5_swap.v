Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N5_swap_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m
        (str ++
        "Before swapping a = " ++
        Z_to_string 2 ++ " , b = " ++ Z_to_string 3 ++ "\n" ++
        "After swapping a = " ++ Z_to_string 3 ++ " , b = " ++ Z_to_string 2 ++ "\n"
      )
  ).

  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_shift; go.
    (* iExists id, (fun str => str ++ "\n")%bs; go. *)
    iExists (_ : ostreamT → ostreamT), (_ : cstring.t → cstring.t); work with br_erefl; go.
    iExists (_ : ostreamT → ostreamT), (_ : cstring.t → cstring.t); work with br_erefl; go.
    banish_string_literals.
    iModIntro.
    work.
    by rewrite -!(assoc_L BS.append).
  Qed.
End with_cpp.
