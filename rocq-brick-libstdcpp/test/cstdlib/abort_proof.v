(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.brick.libstdcpp.test.cstdlib.abort_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "test_abort_guard(int)" with
    (\arg{x} "x" (Vint x)
     \post[Vint x] [| 0 <= x |]%Z).
  Lemma test_abort_guard_ok : verify[source] "test_abort_guard(int)".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  cpp.spec "test_abort_noreturn()" with
    (\post{r}[Vint r] False).
  Lemma test_abort_noreturn_ok : verify[source] "test_abort_noreturn()".
  Proof. verify_spec; go. Qed.
End with_cpp.
