(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.base_logic.lib.spectra.
Require Import skylabs.brick.libstdcpp.cstdio.spec.
Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.cstdio.fputs_cpp.

Import linearity.

(** Each test runs against an output app that accepts exactly the expected
    text, as in the [g4g] tests: the final state [""] means all of it was
    written, in order. *)
Section hello.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  #[local] Abbreviation APP := (output_app (eq "Hello"%bs)).
  Context `{SPECTRA : !appG APP _Σ}.
  #[local] Instance Hello : App.app := mkApp APP.
  Definition OS_hello γ : Ostream :=
    AppHandler Hello (⊤ ∖ ↑refinement_rootNS) masks.default γ.
  Definition gen_X_hello := gen_requester_C Hello.
  Hint Resolve gen_X_hello : sl_opacity.
  Definition bs_dos_steps_hello_C :=
    gen_bs_dos_steps_C Hello.(App.lts) Hello.(App.inG).
  Hint Resolve bs_dos_steps_hello_C : sl_opacity.

  cpp.spec "test_fputs_hello(FILE*)" with
    (\arg{f} "f" (Vptr f)
     \prepost{γ g} f |-> cfile.R (OS_hello γ) g 1$m
     \persist Step.updater Hello (⊤ ∖ ↑refinement_rootNS) γ
     \pre AuthSet.frag γ {[ "Hello"%bs ]}
     \post AuthSet.frag γ {[ ""%bs ]}).
  Lemma test_fputs_hello_ok : verify[source] "test_fputs_hello(FILE*)".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro; go.
  Qed.
End hello.

Section twice.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  #[local] Abbreviation APP := (output_app (eq "abcd"%bs)).
  Context `{SPECTRA : !appG APP _Σ}.
  #[local] Instance Twice : App.app := mkApp APP.
  Definition OS_twice γ : Ostream :=
    AppHandler Twice (⊤ ∖ ↑refinement_rootNS) masks.default γ.
  Definition gen_X_twice := gen_requester_C Twice.
  Hint Resolve gen_X_twice : sl_opacity.
  Definition bs_dos_steps_twice_C :=
    gen_bs_dos_steps_C Twice.(App.lts) Twice.(App.inG).
  Hint Resolve bs_dos_steps_twice_C : sl_opacity.

  (* The first call leaves "cd" to write. *)
  #[local] Instance abcd_steps :
    AnySteps only_output {[ "abcd"%bs ]}
      ((λ x : N, Write x) <$> BS.string_to_bytes "ab") {[ "cd"%bs ]} :=
    initial_any_steps (str := "ab") (rest := "cd").

  cpp.spec "test_fputs_twice(FILE*)" with
    (\arg{f} "f" (Vptr f)
     \prepost{γ g} f |-> cfile.R (OS_twice γ) g 1$m
     \persist Step.updater Twice (⊤ ∖ ↑refinement_rootNS) γ
     \pre AuthSet.frag γ {[ "abcd"%bs ]}
     \post AuthSet.frag γ {[ ""%bs ]}).
  Lemma test_fputs_twice_ok : verify[source] "test_fputs_twice(FILE*)".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro; go.
  Qed.
End twice.

Section std_stream.
  (* Rocq strings have no escapes: the newline is written literally. *)
  #[local] Abbreviation error_line := "error
"%bs.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  #[local] Abbreviation APP := (output_app (eq error_line)).
  Context `{SPECTRA : !appG APP _Σ}.
  #[local] Instance Err : App.app := mkApp APP.
  Definition OS_err γ : Ostream :=
    AppHandler Err (⊤ ∖ ↑refinement_rootNS) masks.default γ.
  Definition gen_X_err := gen_requester_C Err.
  Hint Resolve gen_X_err : sl_opacity.
  Definition bs_dos_steps_err_C :=
    gen_bs_dos_steps_C Err.(App.lts) Err.(App.inG).
  Hint Resolve bs_dos_steps_err_C : sl_opacity.

  (* The caller reads the [stderr] pointer and owns the stream it names. *)
  cpp.spec "test_fputs_stderr()" with
    (\prepost{q f} _global "stderr" |-> ptrR<"_IO_FILE"> q f
     \prepost{γ g} f |-> cfile.R (OS_err γ) g 1$m
     \persist Step.updater Err (⊤ ∖ ↑refinement_rootNS) γ
     \pre AuthSet.frag γ {[ error_line ]}
     \post[Vbool true] AuthSet.frag γ {[ ""%bs ]}).
  Lemma test_fputs_stderr_ok : verify[source] "test_fputs_stderr()".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro; go.
  Qed.
End std_stream.
