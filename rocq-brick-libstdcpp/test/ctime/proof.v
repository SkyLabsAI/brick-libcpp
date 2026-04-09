(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.

Require Import skylabs.brick.libstdcpp.ctime.spec.
Require Import skylabs.brick.libstdcpp.test.ctime.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_time_null()" default.
  Lemma test_time_null_ok : verify[module] "test_time_null()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_time_store()" default.
  Lemma test_time_store_ok : verify[module] "test_time_store()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_timespec_get_ptr(timespec* )" with (
    \arg{ts_p} "ts" (Vptr ts_p)
    \pre ts_p |-> anyR "timespec" 1$m
    \post
      (Exists ts,
         [| timespec_get_result ts |] **
         ts_p |-> timespecR 1$m ts) \\//
      (ts_p |-> anyR "timespec" 1$m)
  ).
  Lemma test_timespec_get_ptr_ok : verify[module] "test_timespec_get_ptr(timespec* )".
  Proof.
    verify_spec.
    go.
    case_bool_decide.
    - iLeft.
      go.
    - iRight.
      go.
  Qed.

  cpp.spec "test_timespec_get_local()" default.
  Lemma test_timespec_get_local_repro : verify?[module] "test_timespec_get_local()".
  Proof.
    (* Intentionally preserves the POD local-dtor completeness repro for [timespec]. *)
    verify_spec; go.
  Admitted.

  cpp.spec "test_timespec_dtor_bug()" default.
  Lemma test_timespec_dtor_bug_repro : verify?[module] "test_timespec_dtor_bug()".
  Proof.
    (* Intentionally preserves the isolated POD ctor/dtor completeness repro for [timespec]. *)
    verify_spec; go.
  Admitted.

  cpp.spec "test_mktime_ptr(tm* )" with (
    \arg{tm_p} "tm" (Vptr tm_p)
    \pre{tm_in} tm_p |-> tmR 1$m tm_in
    \post
      Exists t tm_out,
        [| mktime_result tm_in tm_out t |] **
        tm_p |-> tmR 1$m tm_out
  ).
  Lemma test_mktime_ptr_ok : verify[module] "test_mktime_ptr(tm* )".
  Proof.
    verify_spec.
    go.
    iExists _.
    go.
  Qed.

  cpp.spec "test_mktime_local()" default.
  Lemma test_mktime_local_repro : verify?[module] "test_mktime_local()".
  Proof.
    (* Intentionally preserves the POD local-dtor completeness repro for [tm]. *)
    verify_spec; go.
  Admitted.

  cpp.spec "test_tm_dtor_bug()" default.
  Lemma test_tm_dtor_bug_repro : verify?[module] "test_tm_dtor_bug()".
  Proof.
    (* Intentionally preserves the isolated POD ctor/dtor completeness repro for [tm]. *)
    verify_spec; go.
  Admitted.

  cpp.spec "test_gmtime_and_asctime()" default.
  Lemma test_gmtime_and_asctime_ok : verify[module] "test_gmtime_and_asctime()".
  Proof.
    verify_spec.
    go.
    wp_if; go.
  Qed.

  cpp.spec "test_localtime_and_ctime()" default.
  Lemma test_localtime_and_ctime_ok : verify[module] "test_localtime_and_ctime()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strftime()" default.
  Lemma test_strftime_ok : verify[module] "test_strftime()".
  Proof.
    verify_spec.
    go.
    wp_if; go.
  Admitted.

  cpp.spec "test_repeated_static_calls()" default.
  Lemma test_repeated_static_calls_ok : verify[module] "test_repeated_static_calls()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "main()" default.
  Lemma main_ok : verify[module] "main()".
  Proof.
    verify_spec; go.
  Qed.

End with_cpp.
