(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.

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

  cpp.spec "test_timespec_get()" default.
  Lemma test_timespec_get_ok : verify?[module] "test_timespec_get()".
  Proof.
    verify_spec.
    go.
    (* case_bool_decide; go. *)
    (* TODO: model the synthetic stack-cleanup destructor for [timespec]. *)
  Admitted.

  cpp.spec "tm::tm()" as tm_ctor_spec with
    (\this this
     \post Exists tm, this |-> tmR 1$m tm).

  cpp.spec "test_tm_dtor_bug()" default.
  Lemma test_tm_dtor_bug_ok : verify?[module] "test_tm_dtor_bug()".
  Proof.
    verify_spec; go.
    (* TODO: model the synthetic stack-cleanup destructor for [tm]. *)
  Admitted.

  cpp.spec "test_mktime()" default.
  Lemma test_mktime_ok : verify?[module] "test_mktime()".
  Proof.
    verify_spec; go.
    (* TODO: model the synthetic stack-cleanup destructor for [tm]. *)
  Admitted.

  cpp.spec "test_gmtime_and_asctime()" default.
  Lemma test_gmtime_and_asctime_ok : verify[module] "test_gmtime_and_asctime()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_localtime_and_ctime()" default.
  Lemma test_localtime_and_ctime_ok : verify[module] "test_localtime_and_ctime()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strftime()" default.
  Lemma test_strftime_ok : verify[module] "test_strftime()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_repeated_static_calls()" default.
  Lemma test_repeated_static_calls_ok : verify[module] "test_repeated_static_calls()".
  Proof. verify_spec; go. Qed.

  cpp.spec "main()" default.
  Lemma main_ok : verify[module] "main()".
  Proof. verify_spec; go. Qed.

End with_cpp.
