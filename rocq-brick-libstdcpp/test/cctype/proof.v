(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.stdlib.cassert.spec.
Require Import skylabs.cpp.stdlib.cctype.spec.
Require Import skylabs.cpp.stdlib.test.cctype.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  (* Test verification for isalpha *)
  cpp.spec "test_isalpha()" default.
  Lemma test_isalpha_ok : verify[module] "test_isalpha()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isdigit *)
  cpp.spec "test_isdigit()" default.
  Lemma test_isdigit_ok : verify[module] "test_isdigit()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isalnum *)
  cpp.spec "test_isalnum()" default.
  Lemma test_isalnum_ok : verify[module] "test_isalnum()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isspace *)
  cpp.spec "test_isspace()" default.
  Lemma test_isspace_ok : verify[module] "test_isspace()".
  Proof. verify_spec; go. Qed.

  (* Test verification for islower *)
  cpp.spec "test_islower()" default.
  Lemma test_islower_ok : verify[module] "test_islower()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isupper *)
  cpp.spec "test_isupper()" default.
  Lemma test_isupper_ok : verify[module] "test_isupper()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isprint *)
  cpp.spec "test_isprint()" default.
  Lemma test_isprint_ok : verify[module] "test_isprint()".
  Proof. verify_spec; go. Qed.

  (* Test verification for ispunct *)
  cpp.spec "test_ispunct()" default.
  Lemma test_ispunct_ok : verify[module] "test_ispunct()".
  Proof. verify_spec; go. Qed.

  (* Test verification for iscntrl *)
  cpp.spec "test_iscntrl()" default.
  Lemma test_iscntrl_ok : verify[module] "test_iscntrl()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isgraph *)
  cpp.spec "test_isgraph()" default.
  Lemma test_isgraph_ok : verify[module] "test_isgraph()".
  Proof. verify_spec; go. Qed.

  (* Test verification for isxdigit *)
  cpp.spec "test_isxdigit()" default.
  Lemma test_isxdigit_ok : verify[module] "test_isxdigit()".
  Proof. verify_spec; go. Qed.

  (* Test verification for tolower *)
  cpp.spec "test_tolower()" default.
  Lemma test_tolower_ok : verify[module] "test_tolower()".
  Proof. verify_spec; go. Qed.

  (* Test verification for toupper *)
  cpp.spec "test_toupper()" default.
  Lemma test_toupper_ok : verify[module] "test_toupper()".
  Proof. verify_spec; go. Qed.

  (* Test verification for main *)
  cpp.spec "main()" default.
  Lemma main_ok : verify[module] "main()".
  Proof. verify_spec; go. Qed.

End with_cpp.
