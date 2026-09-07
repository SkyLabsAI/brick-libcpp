(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Require Import skylabs.brick.libstdcpp.compare.pred.

Require Import skylabs.brick.libstdcpp.test.compare.int_point.
Require Import skylabs.brick.libstdcpp.test.compare.weak_bucket.
Require Import skylabs.brick.libstdcpp.test.compare.floating_box.

Require Import skylabs.brick.libstdcpp.test.compare.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "TestIntegralSpaceship()" as test_integral_spaceship with (
    \prepost{q_globals} std.compare.strong_ordering_globals q_globals
    \post[Vbool true] emp).

  (* TODO: quiet_NaN returns an arbitrary quiet NaN, not necessarily this one. *)
  cpp.spec "std::numeric_limits<double>::quiet_NaN()" as test_quiet_NaN from source with (
    \post[Vfloat float_type.Fdouble (proj1_sig (float_value.default_nan float_type.Fdouble))] emp).

  cpp.spec "TestFloatingSpaceship()" as test_floating_spaceship with (
    \prepost{q_globals} std.compare.partial_ordering_globals q_globals
    \post[Vbool true] emp).

  cpp.spec "TestComparisonCategories()" as test_comparison_categories with (
    \prepost{q_globals} std.compare.compare_globals q_globals
    \post[Vbool true] emp).

  cpp.spec "TestDefaultedIntegerClass()" as test_defaulted_integer_class with (
    \prepost{q_globals} std.compare.strong_ordering_globals q_globals
    \post[Vbool true] emp).

  cpp.spec "TestWeakOrderingClass()" as test_weak_ordering_class with (
    \prepost{q_globals} std.compare.weak_ordering_globals q_globals
    \post[Vbool true] emp).

  cpp.spec "TestDefaultedFloatingClass()" as test_defaulted_floating_class with (
    \prepost{q_globals} std.compare.partial_ordering_globals q_globals
    \prepost std.compare.strong_ordering_globals q_globals
    \post[Vbool true] emp).

  cpp.spec "main()" as main with (
    \prepost{q_globals} std.compare.compare_globals q_globals
    \post[Vint 0] emp).

  Definition specs :=
    int_point_specs **
    weak_bucket_specs **
    floating_box_specs **
    test_integral_spaceship **
    test_quiet_NaN **
    test_floating_spaceship **
    test_comparison_categories **
    test_defaulted_integer_class **
    test_weak_ordering_class **
    test_defaulted_floating_class **
    main.

End with_cpp.
