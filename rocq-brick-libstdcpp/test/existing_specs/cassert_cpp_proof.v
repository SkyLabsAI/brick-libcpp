
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.test.existing_specs.cassert_cpp.

Require Import skylabs.auto.cpp.prelude.proof.
Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : cassert_cpp.source ⊧ σ}.

  cpp.spec "cassert_client::assert_true_success()" as assert_true_success_spec from cassert_cpp.source with (
    \post emp).

  Lemma assert_true_success_ok :
    verify[cassert_cpp.source] "cassert_client::assert_true_success()".
  Proof.

    verify_spec.

    go $usenamed=true.

  Qed.

  cpp.spec "cassert_client::glibc_backend_guarded(bool)" as glibc_backend_guarded_spec from cassert_cpp.source with (
    \arg{condition} "condition" (Vbool condition)
    \require condition = true
    \post emp).

  cpp.spec "cassert_client::glibc_assert_macro_guarded(bool)" as glibc_assert_macro_guarded_spec from cassert_cpp.source with (
    \arg{condition} "condition" (Vbool condition)
    \require condition = true
    \post emp).

  cpp.spec "cassert_client::glibc_success_composition()" as glibc_success_composition_spec from cassert_cpp.source with (
    \post emp).

  Lemma glibc_backend_guarded_ok :
    verify[cassert_cpp.source] "cassert_client::glibc_backend_guarded(bool)".
  Proof.

    verify_spec.

    go $usenamed=true.

  Qed.

  Lemma glibc_assert_macro_guarded_ok :
    verify[cassert_cpp.source] "cassert_client::glibc_assert_macro_guarded(bool)".
  Proof.
    verify_spec.
    go $usenamed=true.
  Qed.

  Lemma glibc_success_composition_ok :
    verify[cassert_cpp.source] "cassert_client::glibc_success_composition()".
  Proof.
    verify_spec.

    go $usenamed=true.

  Qed.

  (* A true-required caller cannot enter the backend guarded by !condition. *)
  Lemma assert_fail_guard_unreachable (condition : bool) :
    condition = true -> negb condition = true -> False.
  Proof.
    destruct condition; cbn; congruence.
  Qed.
End with_cpp.
