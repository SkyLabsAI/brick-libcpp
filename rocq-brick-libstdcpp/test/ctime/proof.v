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

  cpp.spec "test_clock()" default.
  Lemma test_clock_ok : verify[module] "test_clock()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_time_null()" default.
  Lemma test_time_null_ok : verify[module] "test_time_null()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_time_store()" default.
  Lemma test_time_store_ok : verify[module] "test_time_store()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_timespec_get(timespec* )" default.
  Lemma test_timespec_get_ok : verify[module] "test_timespec_get(timespec* )".
  Proof.
    verify_spec.
  Admitted.

  cpp.spec "test_mktime(tm* )" default.
  Lemma test_mktime_ok : verify[module] "test_mktime(tm* )".
  Proof. admit. Admitted.

  cpp.spec "test_gmtime(long const* )" default.
  Lemma test_gmtime_ok : verify[module] "test_gmtime(long const* )".
  Proof. admit. Admitted.

  cpp.spec "test_asctime(tm const* )" default.
  Lemma test_asctime_ok : verify[module] "test_asctime(tm const* )".
  Proof. admit. Admitted.

  cpp.spec "test_localtime(long const* )" default.
  Lemma test_localtime_ok : verify[module] "test_localtime(long const* )".
  Proof. admit. Admitted.

  cpp.spec "test_ctime(long const* )" default.
  Lemma test_ctime_ok : verify[module] "test_ctime(long const* )".
  Proof. admit. Admitted.

  cpp.spec "test_strftime(char* , unsigned long, tm const* )" default.
  Lemma test_strftime_ok : verify[module] "test_strftime(char* , unsigned long, tm const* )".
  Proof. admit. Admitted.

  cpp.spec "test_repeated_static_calls(long const* )" default.
  Lemma test_repeated_static_calls_ok : verify[module] "test_repeated_static_calls(long const* )".
  Proof. admit. Admitted.

  cpp.spec "main()" default.
  Lemma main_ok : verify[module] "main()".
  Proof. admit. Admitted.

End with_cpp.
