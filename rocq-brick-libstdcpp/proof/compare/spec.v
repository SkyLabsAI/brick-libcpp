(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.compare.pred.
Require Import skylabs.brick.libstdcpp.compare.inc_compare_cpp.

#[local] Open Scope Z_scope.

NES.Begin std.compare.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  cpp.spec "std::strong_ordering::strong_ordering(const std::strong_ordering&)" as strong_ordering_copy_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> strong_orderingR q v
    \post this |-> strong_orderingR 1$m v).

  cpp.spec "std::strong_ordering::strong_ordering(std::strong_ordering&&)" as strong_ordering_move_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> strong_orderingR q v
    \post this |-> strong_orderingR 1$m v).

  cpp.spec "std::strong_ordering::~strong_ordering()" as strong_ordering_dtor from source with (
    \this this
    \pre{v} this |-> strong_orderingR 1$m v
    \post emp).

  cpp.spec "std::partial_ordering::~partial_ordering()" as partial_ordering_dtor from source with (
    \this this
    \pre{v} this |-> partial_orderingR 1$m v
    \post emp).

  cpp.spec "std::partial_ordering::partial_ordering(const std::partial_ordering&)" as partial_ordering_copy_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> partial_orderingR q v
    \post this |-> partial_orderingR 1$m v).

  cpp.spec "std::partial_ordering::partial_ordering(std::partial_ordering&&)" as partial_ordering_move_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> partial_orderingR q v
    \post this |-> partial_orderingR 1$m v).

  cpp.spec "std::weak_ordering::weak_ordering(const std::weak_ordering&)" as weak_ordering_copy_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> weak_orderingR q v
    \post this |-> weak_orderingR 1$m v).

  cpp.spec "std::weak_ordering::weak_ordering(std::weak_ordering&&)" as weak_ordering_move_ctor from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q v} other |-> weak_orderingR q v
    \post this |-> weak_orderingR 1$m v).

  cpp.spec "std::weak_ordering::~weak_ordering()" as weak_ordering_dtor from source with (
    \this this
    \pre{v} this |-> weak_orderingR 1$m v
    \post emp).

  cpp.spec "std::operator==(std::strong_ordering, std::strong_ordering)" as strong_ordering_eq from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> strong_orderingR q_lhs lhs_v
    \prepost{q_rhs rhs_v} rhs |-> strong_orderingR q_rhs rhs_v
    \post[Vbool (bool_decide (lhs_v = rhs_v))] emp).

  cpp.spec "std::operator==(std::partial_ordering, std::partial_ordering)" as partial_ordering_eq from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> partial_orderingR q_lhs lhs_v
    \prepost{q_rhs rhs_v} rhs |-> partial_orderingR q_rhs rhs_v
    \post[Vbool (bool_decide (lhs_v = rhs_v))] emp).

  cpp.spec "std::operator==(std::weak_ordering, std::weak_ordering)" as weak_ordering_eq from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> weak_orderingR q_lhs lhs_v
    \prepost{q_rhs rhs_v} rhs |-> weak_orderingR q_rhs rhs_v
    \post[Vbool (bool_decide (lhs_v = rhs_v))] emp).

  cpp.spec "std::strong_ordering::operator std::partial_ordering() const"
      as strong_to_partial from source with (
      \this this
      \prepost{q v} this |-> strong_orderingR q v
      \post{result}[Vptr result] result |-> partial_orderingR 1$m (Some v)).

  cpp.spec "std::weak_ordering::operator std::partial_ordering() const"
      as weak_to_partial from source with (
      \this this
      \prepost{q v} this |-> weak_orderingR q v
      \post{result}[Vptr result] result |-> partial_orderingR 1$m (Some v)).

  cpp.spec "std::__cmp_cat::__unspec::__unspec(std::__cmp_cat::__unspec*)" as unspec_ctor from source with (
    \this this
    \arg{p} "" (Vptr p)
    \pre [| p = nullptr |]
    \post this |-> unspecR 1$m).

  cpp.spec "std::__cmp_cat::__unspec::~__unspec()" as unspec_dtor from source with (
    \this this
    \pre this |-> unspecR 1$m
    \post emp).

  cpp.spec "std::operator==(std::partial_ordering, std::__cmp_cat::__unspec)" as partial_ordering_eq_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> partial_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Some Eq))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<(std::partial_ordering, std::__cmp_cat::__unspec)" as partial_ordering_lt_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> partial_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Some Lt))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator>(std::partial_ordering, std::__cmp_cat::__unspec)" as partial_ordering_gt_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> partial_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Some Gt))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<=>(std::partial_ordering, std::__cmp_cat::__unspec)" as partial_ordering_cmp_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> partial_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post{result}[Vptr result] result |-> partial_orderingR 1$m lhs_v ** rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<(std::strong_ordering, std::__cmp_cat::__unspec)" as strong_ordering_lt_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> strong_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Lt))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator==(std::strong_ordering, std::__cmp_cat::__unspec)" as strong_ordering_eq_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> strong_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Eq))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator>(std::strong_ordering, std::__cmp_cat::__unspec)" as strong_ordering_gt_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> strong_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Gt))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<=>(std::strong_ordering, std::__cmp_cat::__unspec)" as strong_ordering_cmp_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> strong_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post{result}[Vptr result] result |-> strong_orderingR 1$m lhs_v ** rhs |-> unspecR q_rhs).

  cpp.spec "std::operator==(std::weak_ordering, std::__cmp_cat::__unspec)" as weak_ordering_eq_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> weak_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Eq))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator>(std::weak_ordering, std::__cmp_cat::__unspec)" as weak_ordering_gt_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> weak_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post[Vbool (bool_decide (lhs_v = Gt))] rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<=>(std::weak_ordering, std::__cmp_cat::__unspec)" as weak_ordering_cmp_unspec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q_lhs lhs_v} lhs |-> weak_orderingR q_lhs lhs_v
    \pre{q_rhs} rhs |-> unspecR q_rhs
    \post{result}[Vptr result] result |-> weak_orderingR 1$m lhs_v ** rhs |-> unspecR q_rhs).

  cpp.spec "std::operator<(std::__cmp_cat::__unspec, std::partial_ordering)" as unspec_lt_partial_ordering from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \pre{q_lhs} lhs |-> unspecR q_lhs
    \prepost{q_rhs rhs_v} rhs |-> partial_orderingR q_rhs rhs_v
    \post[Vbool (bool_decide (rhs_v = Some Gt))] lhs |-> unspecR q_lhs).

  cpp.spec "std::operator<=>(std::__cmp_cat::__unspec, std::partial_ordering)" as unspec_cmp_partial_ordering from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \pre{q_lhs} lhs |-> unspecR q_lhs
    \prepost{q_rhs rhs_v} rhs |-> partial_orderingR q_rhs rhs_v
    \post{result}[Vptr result] result |-> partial_orderingR 1$m (CompOpp <$> rhs_v) ** lhs |-> unspecR q_lhs).

  cpp.spec "std::operator>(std::__cmp_cat::__unspec, std::strong_ordering)" as unspec_gt_strong_ordering from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \pre{q_lhs} lhs |-> unspecR q_lhs
    \prepost{q_rhs rhs_v} rhs |-> strong_orderingR q_rhs rhs_v
    \post[Vbool (bool_decide (rhs_v = Lt))] lhs |-> unspecR q_lhs).

  cpp.spec "std::operator<=>(std::__cmp_cat::__unspec, std::strong_ordering)" as unspec_cmp_strong_ordering from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \pre{q_lhs} lhs |-> unspecR q_lhs
    \prepost{q_rhs rhs_v} rhs |-> strong_orderingR q_rhs rhs_v
    \post{result}[Vptr result] result |-> strong_orderingR 1$m (CompOpp rhs_v) ** lhs |-> unspecR q_lhs).

  cpp.spec "std::operator<=>(std::__cmp_cat::__unspec, std::weak_ordering)" as unspec_cmp_weak_ordering from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \pre{q_lhs} lhs |-> unspecR q_lhs
    \prepost{q_rhs rhs_v} rhs |-> weak_orderingR q_rhs rhs_v
    \post{result}[Vptr result] result |-> weak_orderingR 1$m (CompOpp rhs_v) ** lhs |-> unspecR q_lhs).

  cpp.spec "std::is_eq(std::partial_ordering)" as is_eq from source with (
    \arg{cmp} "__cmp" (Vptr cmp)
    \prepost{q v} cmp |-> partial_orderingR q v
    \post[Vbool (bool_decide (v = Some Eq))] emp).

  cpp.spec "std::is_lt(std::partial_ordering)" as is_lt from source with (
    \arg{cmp} "__cmp" (Vptr cmp)
    \prepost{q v} cmp |-> partial_orderingR q v
    \post[Vbool (bool_decide (v = Some Lt))] emp).

  cpp.spec "std::is_gt(std::partial_ordering)" as is_gt from source with (
    \arg{cmp} "__cmp" (Vptr cmp)
    \prepost{q v} cmp |-> partial_orderingR q v
    \post[Vbool (bool_decide (v = Some Gt))] emp).

  Definition specs :=
    strong_ordering_copy_ctor **
    strong_ordering_move_ctor **
    strong_ordering_dtor **
    partial_ordering_dtor **
    partial_ordering_copy_ctor **
    partial_ordering_move_ctor **
    weak_ordering_copy_ctor **
    weak_ordering_move_ctor **
    weak_ordering_dtor **
    strong_ordering_eq **
    partial_ordering_eq **
    weak_ordering_eq **
    strong_to_partial **
    weak_to_partial **
    unspec_ctor **
    unspec_dtor **
    partial_ordering_eq_unspec **
    partial_ordering_lt_unspec **
    partial_ordering_gt_unspec **
    partial_ordering_cmp_unspec **
    strong_ordering_lt_unspec **
    strong_ordering_eq_unspec **
    strong_ordering_gt_unspec **
    strong_ordering_cmp_unspec **
    weak_ordering_eq_unspec **
    weak_ordering_gt_unspec **
    weak_ordering_cmp_unspec **
    unspec_lt_partial_ordering **
    unspec_cmp_partial_ordering **
    unspec_gt_strong_ordering **
    unspec_cmp_strong_ordering **
    unspec_cmp_weak_ordering **
    is_eq **
    is_lt **
    is_gt.
  #[global] Hint Opaque specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive specs.

End with_cpp.

NES.End std.compare.
