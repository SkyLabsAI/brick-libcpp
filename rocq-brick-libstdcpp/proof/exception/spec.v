(*
 * Copyright (c) 2025 BlueRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.

Require Import skylabs.brick.libstdcpp.exception.inc_exception_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  cpp.spec "std::terminate()" as terminate_spec with
      (\post False).

  cpp.spec "std::set_terminate(void(*)())" as set_terminate_spec with
      (\arg{fp} "terminate_handler" (Vptr fp)
       \pre False
       \post{fp}[Vptr fp] emp).

  cpp.spec "std::get_terminate()" as get_terminate_spec with
      (\pre False
       \post{fp}[Vptr fp] emp).

End with_cpp.
