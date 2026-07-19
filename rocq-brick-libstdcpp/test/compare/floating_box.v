(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Require Import skylabs.brick.libstdcpp.compare.pred.
Require Import skylabs.brick.libstdcpp.test.compare.test_cpp.

Record FloatingBox := {
  floating_box_value : float_type.car float_type.Fdouble;
}.
#[only(eq_dec)] derive FloatingBox.

#[global] Instance SplitRecord_FloatingBox : SplitRecord FloatingBox := {}.

Definition floating_box_compare (p p' : FloatingBox) : option comparison :=
  float_value.value_compare
    p.(floating_box_value) p'.(floating_box_value).


sl.lock
Definition FloatingBoxR `{Σ : cpp_logic, σ : genv} (q : cQp.t) (p : FloatingBox) : Rep :=
  structR "FloatingBox" q **
  _field "FloatingBox::value" |-> primR Tdouble q (Vfloat float_type.Fdouble p.(floating_box_value)).
#[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive FloatingBoxR.


Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "FloatingBox::~FloatingBox()" as floating_box_dtor with (
    \this this
    \pre{m} this |-> FloatingBoxR 1$m m
    \post emp).

  cpp.spec "FloatingBox::operator==(const FloatingBox&) const" as floating_box_eq with (
    \this this
    \arg{other} "" (Vref other)
    \prepost{q_this m} this |-> FloatingBoxR q_this m
    \prepost{q_other m'} other |-> FloatingBoxR q_other m'
    \post[Vbool (bool_decide (floating_box_compare m m' = Some Eq))] emp).

  cpp.spec "FloatingBox::operator<=>(const FloatingBox&) const" as floating_box_spaceship with (
    \this this
    \arg{other} "" (Vref other)
    \prepost{q_globals} std.compare.partial_ordering_globals q_globals
    \prepost std.compare.strong_ordering_globals q_globals
    \prepost{q_this m} this |-> FloatingBoxR q_this m
    \prepost{q_other m'} other |-> FloatingBoxR q_other m'
    \post{result}[Vptr result]
      result |-> std.compare.partial_orderingR 1$m (floating_box_compare m m')).

  Definition floating_box_specs :=
    floating_box_dtor **
    floating_box_eq **
    floating_box_spaceship.
  #[global] Hint Opaque floating_box_specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive floating_box_specs.
End with_cpp.
