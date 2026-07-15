
(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cwctype.spec.
Require Import skylabs.brick.libstdcpp.test.cwctype.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_letter_and_number_classes()" default.
  Lemma test_letter_and_number_classes_ok :
    verify[module] "test_letter_and_number_classes()".
Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_space_and_display_classes()" default.
  Lemma test_space_and_display_classes_ok :
    verify[module] "test_space_and_display_classes()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_weof_boundary()" default.
  Lemma test_weof_boundary_ok :
    verify[module] "test_weof_boundary()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_case_conversion()" default.
  Lemma test_case_conversion_ok :
    verify[module] "test_case_conversion()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "test_classification_conversion_composition()" default.
  Lemma test_classification_conversion_composition_ok :
    verify[module] "test_classification_conversion_composition()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "main()" default.
  Lemma main_ok : verify[module] "main()".
  Proof. verify_spec; go $usenamed=true. Qed.

  Lemma invalid_raw_wint_is_outside_contract :
    ~ ((4294967294%Z) = cwctype_weof \/
       (0 <= (4294967294%Z) <= 2147483647)%Z).
  Proof. rewrite /cwctype_weof; lia. Qed.

End with_cpp.
