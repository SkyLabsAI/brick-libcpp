(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.test.vector.test_cpp.
Require Import skylabs.auto.cpp.prelude.test.

(** The size constructors' specs are registered under the signatures of
    [vector.cons], which take the allocator by [const&]. *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Goal SpecFor.C source
    "std::vector<int, std::allocator<int>>::vector(unsigned long, const std::allocator<int>&)"%cpp_name.
  Proof. typeclasses eauto. Qed.

  Goal SpecFor.C source
    "std::vector<int, std::allocator<int>>::vector(unsigned long, const int&, const std::allocator<int>&)"%cpp_name.
  Proof. typeclasses eauto. Qed.
End with_cpp.
