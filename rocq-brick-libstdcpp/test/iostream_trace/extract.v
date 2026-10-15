(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.iostream_trace.spec.

(** * [in >> b] may store nothing

    If the sentry fails, e.g. at the end of the input or after an earlier failed
    extraction, nothing is stored ([istream.formatted.reqmts]/1; libstdc++
    assigns only [if (__cerb)]). So [uninit] reads an indeterminate value on
    empty input, which is undefined behavior (no clang sanitizer reports it:
    libstdc++ is not instrumented for MSan). The spec takes an initialized
    argument, so [init] verifies and [uninit] does not. *)
cpp.prog source flags "-std=c++20 -stdlib=libstdc++" prog cpp:{{
  #include <istream>
  int init(std::istream &in) {
    int b = 0;
    in >> b;
    return b;
  }
  int uninit(std::istream &in) {
    int b;
    in >> b;
    return b;
  }
}}.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "init(std::istream&)" from source as init_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{isM} inp |-> istreamR 1$m isM
    \post{n}[Vint n] ∃ isM', inp |-> istreamR 1$m isM').

  Lemma init_ok : verify[source] init_spec.
  Proof. verify_spec; go. Qed.

  cpp.spec "uninit(std::istream&)" from source as uninit_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{isM} inp |-> istreamR 1$m isM
    \post{n}[Vint n] ∃ isM', inp |-> istreamR 1$m isM').

  (** Stuck at the call: [b] holds no value. *)
  Lemma uninit_ok : verify[source] uninit_spec.
  Proof. verify_spec; go. Fail Qed. Abort.
End with_cpp.
