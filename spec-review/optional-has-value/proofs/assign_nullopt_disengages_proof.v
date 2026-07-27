
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (MOD : test_cpp.source ⊧ σ).

  cpp.spec "assign_nullopt_disengages()" from test_cpp.source with
    (\prepost _global "std::nullopt" |-> structR nulloptN 1$m
     \post emp).

  Lemma verify_assign_nullopt_disengages :
    verify[test_cpp.source] "assign_nullopt_disengages()".
  Proof.
    verify_spec'.
    iClear select (▷ (_global "std::nullopt" |-> structR nulloptN 1$c))%I.
    repeat iRevert select (▷ _)%I.
    repeat iIntros "#?".
    iModIntro. iIntros (POST vals) "Hpre".
    go $usenamed=true.
    wname [ (value_addr |-> optionalR 1$m (Some 5)) ] "Hvalue".
    iDestruct (observe (type_ptr optionalT value_addr) with "Hvalue") as "#Htype".
    iDestruct (type_ptr_reference_to with "Htype") as "#Href".
    iExists (Some 5).
    iFrame "Hvalue Href".
    go $usenamed=true.
    iExists (1)%cQp, None.
    go $usenamed=true.
    iExists None.
    go $usenamed=true.
  Qed.
End with_cpp.
