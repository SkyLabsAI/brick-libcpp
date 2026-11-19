(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.brick.libstdcpp.cstdlib.inc_cstdlib_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** <<abort>> ends the process abnormally and never returns (C11
      7.22.4.1), like [std::terminate]. Code after a call is unreachable. *)
  cpp.spec "abort" as abort_spec with
      (\post False).
End with_cpp.
