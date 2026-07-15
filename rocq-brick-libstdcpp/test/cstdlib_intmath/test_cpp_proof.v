(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstdlib_intmath.spec.
Require Import skylabs.brick.libstdcpp.test.cstdlib_intmath.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_abs_int()" default.
  Lemma test_abs_int_ok : verify[module] "test_abs_int()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_abs_long()" default.
  Lemma test_abs_long_ok : verify[module] "test_abs_long()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_abs_long_long()" default.
  Lemma test_abs_long_long_ok : verify[module] "test_abs_long_long()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_div_int()" default.
  Lemma test_div_int_ok : verify[module] "test_div_int()".
  Proof. verify_spec; go $usenamed=true. 
all: repeat (iExists _); iFrame.

go $usenamed=true.

Qed.


  cpp.spec "test_div_long()" default.
  Lemma test_div_long_ok : verify[module] "test_div_long()".
  Proof. verify_spec; go $usenamed=true. 
all: repeat (iExists _); iFrame.
go $usenamed=true.
Qed.


  cpp.spec "test_div_long_long()" default.
  Lemma test_div_long_long_ok : verify[module] "test_div_long_long()".
  Proof. verify_spec; go $usenamed=true. 
all: repeat (iExists _); iFrame.
go $usenamed=true.
Qed.


  cpp.spec "test_intmath_composition()" default.
  Lemma test_intmath_composition_ok :
    verify[module] "test_intmath_composition()".
  Proof. verify_spec; go $usenamed=true. 
all: repeat (iExists _); iFrame.
go $usenamed=true.
Qed.


End with_cpp.
