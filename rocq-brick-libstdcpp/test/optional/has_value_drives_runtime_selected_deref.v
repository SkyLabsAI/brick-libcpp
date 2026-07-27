
Require Import skylabs.brick.libstdcpp.test.optional.clients_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.optional.spec.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : !clients_cpp.source ⊧ σ}.
  cpp.spec "check_runtime_selected_optional(bool)"
    from clients_cpp.source as check_runtime_selected_optional_helper_spec with (
      \with{choose_present : bool}
      \arg{choose_present} "choose_present" (Vbool choose_present)
      \post emp
    ).

  cpp.spec "has_value_drives_runtime_selected_deref()"
    from clients_cpp.source
    as has_value_drives_runtime_selected_deref_spec with (\post emp).
  
Lemma has_value_drives_runtime_selected_deref_proof :
    verify[clients_cpp.module] "has_value_drives_runtime_selected_deref()".

  Proof using MOD.

    verify_spec.

    go $usenamed=true.

    iExists _.

    go $usenamed=true.

    iExists _.

    go $usenamed=true.

  Unshelve.

  1: exact true.

  exact false.

  Qed.

End with_cpp.
