(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Require Import skylabs.brick.libstdcpp.compare.pred.
Require Import skylabs.brick.libstdcpp.test.compare.test_cpp.

Record IntPoint := {
  int_point_x : Z;
  int_point_y : Z;
}.
#[only(eq_dec)] derive IntPoint.

#[global] Instance SplitRecord_IntPoint : SplitRecord IntPoint := {}.

Definition int_point_compare (p p' : IntPoint) : comparison :=
  compare.compare_lex
    (Z.compare p.(int_point_x) p'.(int_point_x))
    (fun _ => Z.compare p.(int_point_y) p'.(int_point_y)).

sl.lock
Definition IntPointR `{Σ : cpp_logic, σ : genv} (q : cQp.t) (p : IntPoint) : Rep :=
  structR "IntPoint" q **
  _field "IntPoint::x" |-> primR Tint q (Vint p.(int_point_x)) **
  _field "IntPoint::y" |-> primR Tint q (Vint p.(int_point_y)).
#[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive IntPointR.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "IntPoint::~IntPoint()" as int_point_dtor with (
    \this this
    \pre{m} this |-> IntPointR 1$m m
    \post emp).

  cpp.spec "IntPoint::operator==(const IntPoint&) const" as int_point_eq with (
    \this this
    \arg{other} "" (Vref other)
    \prepost{q_this m} this |-> IntPointR q_this m
    \prepost{q_other m'} other |-> IntPointR q_other m'
    \post[Vbool (bool_decide (m = m'))] emp).

  cpp.spec "IntPoint::operator<=>(const IntPoint&) const" as int_point_spaceship with (
    \this this
    \arg{other} "" (Vref other)
    \prepost{q_globals} std.compare.strong_ordering_globals q_globals
    \prepost{q_this m} this |-> IntPointR q_this m
    \prepost{q_other m'} other |-> IntPointR q_other m'
    \post{result}[Vptr result]
      result |-> std.compare.strong_orderingR 1$m (int_point_compare m m')).

  Definition int_point_specs :=
    int_point_dtor **
    int_point_eq **
    int_point_spaceship.
  #[global] Hint Opaque int_point_specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive int_point_specs.

End with_cpp.
