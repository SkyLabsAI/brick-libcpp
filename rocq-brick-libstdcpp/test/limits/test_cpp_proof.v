(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.limits.spec.
Require Import skylabs.brick.libstdcpp.test.limits.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "SizeTMax(unsigned long)" as size_t_max_spec with (
    \arg{n} "n" (Vn n)
    \post[Vbool true] emp).

  Lemma size_t_max_ok : verify[source] size_t_max_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Int64Max()" as int64_max_spec with (\post[Vbool true] emp).

  Lemma int64_max_ok : verify[source] int64_max_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "IntMin()" as int_min_spec with (\post[Vbool true] emp).

  Lemma int_min_ok : verify[source] int_min_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "UnsignedMin()" as unsigned_min_spec with (\post[Vbool true] emp).

  Lemma unsigned_min_ok : verify[source] unsigned_min_spec.
  Proof using MOD. verify_spec; go. Qed.

End with_cpp.
