(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Import skylabs.auto.cpp.proof.

#[local] Open Scope Z_scope.

NES.Begin std.compare.

  Definition ordering_value (v : comparison) : Z :=
    match v with
    | Lt => -1
    | Eq => 0
    | Gt => 1
    end.

  Definition partial_ordering_value (v : option comparison) : Z :=
    match v with
    | Some v => ordering_value v
    | None => 2
    end.

  sl.lock
  Definition strong_orderingR `{Σ : cpp_logic, σ : genv}
      (q : cQp.t) (v : comparison) : Rep :=
    structR "std::strong_ordering" q **
    _field "std::strong_ordering::_M_value" |-> primR Tschar q (Vint (ordering_value v)).
  #[only(cfractional,cfracvalid,ascfractional,timeless,type_ptr,lazy_unfold(global))] derive strong_orderingR.
  Definition _at_strong_orderingR_learn `{Σ : cpp_logic, σ : genv} :
    AtLearnEqF1 strong_orderingR := ltac:(solve_learnable).
  #[global] Hint Resolve _at_strong_orderingR_learn : sl_opacity.


  sl.lock
  Definition partial_orderingR `{Σ : cpp_logic, σ : genv}
      (q : cQp.t) (v : option comparison) : Rep :=
    structR "std::partial_ordering" q **
    _field "std::partial_ordering::_M_value" |-> primR Tschar q (Vint (partial_ordering_value v)).
  #[only(cfractional,cfracvalid,ascfractional,timeless,type_ptr,lazy_unfold(global))] derive partial_orderingR.
  Definition _at_partial_orderingR_learn `{Σ : cpp_logic, σ : genv} :
    AtLearnEqF1 partial_orderingR := ltac:(solve_learnable).
  #[global] Hint Resolve _at_partial_orderingR_learn : sl_opacity.

  sl.lock
  Definition weak_orderingR `{Σ : cpp_logic, σ : genv}
      (q : cQp.t) (v : comparison) : Rep :=
    structR "std::weak_ordering" q **
    _field "std::weak_ordering::_M_value" |-> primR Tschar q (Vint (ordering_value v)).
  #[only(cfractional,cfracvalid,ascfractional,timeless,type_ptr,lazy_unfold(global))] derive weak_orderingR.
  Definition _at_weak_orderingR_learn `{Σ : cpp_logic, σ : genv} :
    AtLearnEqF1 weak_orderingR := ltac:(solve_learnable).
  #[global] Hint Resolve _at_weak_orderingR_learn : sl_opacity.

  sl.lock
  Definition unspecR `{Σ : cpp_logic, σ : genv} (q : cQp.t) : Rep :=
    structR "std::__cmp_cat::__unspec" q ** emp.
  #[only(cfractional,cfracvalid,ascfractional,timeless,type_ptr,lazy_unfold(global))] derive unspecR.

  #[global] Abbreviation strong_ordering_globals q := (
    _global "std::strong_ordering::less" |-> strong_orderingR q Lt **
    _global "std::strong_ordering::equal" |-> strong_orderingR q Eq **
    _global "std::strong_ordering::greater" |-> strong_orderingR q Gt).

  #[global] Abbreviation weak_ordering_globals q := (
    _global "std::weak_ordering::less" |-> weak_orderingR q Lt **
    _global "std::weak_ordering::equivalent" |-> weak_orderingR q Eq **
    _global "std::weak_ordering::greater" |-> weak_orderingR q Gt).

  #[global] Abbreviation partial_ordering_globals q := (
    _global "std::partial_ordering::less" |-> partial_orderingR q (Some Lt) **
    _global "std::partial_ordering::equivalent" |-> partial_orderingR q (Some Eq) **
    _global "std::partial_ordering::greater" |-> partial_orderingR q (Some Gt) **
    _global "std::partial_ordering::unordered" |-> partial_orderingR q None).

  #[global] Abbreviation compare_globals q := (
    strong_ordering_globals q **
    weak_ordering_globals q **
    partial_ordering_globals q).

NES.End std.compare.
