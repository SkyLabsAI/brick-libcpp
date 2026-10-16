(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.

(** * Specifications for <<std::numeric_limits<T>::min>> and <<max>>

    <https://eel.is/c++draft/numeric.limits.members>

    Every integer type has its own explicit specialization of
    <<std::numeric_limits>>, so the specs are stated once for [Tnum sz sgn]
    and named per specialization. Calls that are not constant-folded reach
    these as ordinary calls. Both functions are total, so no call is
    undefined. Floating-point, character and <<bool>> specializations are not
    covered. *)
NES.Begin std.numeric_limits.

  #[global] Abbreviation N ty := (Ninst "std::numeric_limits" [Atype ty]).

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.
    Context (sz : int_rank) (sgn : signed).

    #[local] Abbreviation ty := (Tnum sz sgn).

    (** <<static constexpr T min() noexcept;>> -- the least finite value of [T]. *)
    Definition min :=
      specify.template.func (Nscoped (N ty) (Nid "min")) [] ty [] $
        \post[Vint (int_rank.min_val sz sgn)] emp.
    #[global] Hint Opaque min : sl_opacity.
    #[global] Arguments min : simpl never.
    Definition SpecFor_min := RegisterSpec min.
    #[global] Existing Instance SpecFor_min.

    (** <<static constexpr T max() noexcept;>> -- the greatest finite value of [T]. *)
    Definition max :=
      specify.template.func (Nscoped (N ty) (Nid "max")) [] ty [] $
        \post[Vint (int_rank.max_val sz sgn)] emp.
    #[global] Hint Opaque max : sl_opacity.
    #[global] Arguments max : simpl never.
    Definition SpecFor_max := RegisterSpec max.
    #[global] Existing Instance SpecFor_max.

    Definition specs := min ** max.
    #[global] Hint Opaque specs : typeclass_instances sl_opacity.
    #[only(knowledge)] derive specs.
  End with_cpp.

NES.End std.numeric_limits.
