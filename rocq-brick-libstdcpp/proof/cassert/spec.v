(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.

Require Import skylabs.brick.libstdcpp.cassert.inc_cassert_cpp.

#[local] Set Primitive Projections.

NES.Begin std.cassert.
Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  Definition assert_fail_wpp : WpSpec_cpp :=
    (\arg{assertion_p} "assertion" (Vptr assertion_p)
       \arg{file_p} "file"           (Vptr file_p)
       \arg{line} "assertion"        (Vn line)
       \arg{function_p} "function"   (Vptr function_p)
       \pre False
       \post False).

  (* The core implementation of the <<assert>> macro.
  Name depends on system and configuration. *)
  #[ignore_missing]
  cpp.spec "__assert_fail" as assert_fail_spec with
    (Reduce assert_fail_wpp).

  #[ignore_missing]
  cpp.spec "__assert_rtn" as assert_rtn_spec with
    (Reduce assert_fail_wpp).

  Definition specs :=
    assert_fail_spec ** assert_rtn_spec.
  #[global] Hint Opaque specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive specs.
End with_cpp.

NES.End std.cassert.
