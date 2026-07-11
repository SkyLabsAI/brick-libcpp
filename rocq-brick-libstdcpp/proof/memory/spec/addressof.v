Require Import skylabs.auto.cpp.spec.

Require Import skylabs.brick.libstdcpp.memory.inc_hpp.
Require Import skylabs.brick.libstdcpp.memory.inc_hpp_templates.

NES.Begin memory.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    Section with_ty.
      Context (ty : type).
      Definition __addressof_spec :=
        specify.template.func "std::__addressof" [Atype ty] (Tptr ty) [Tref ty] $
          \arg{mp} "" (Vref mp)
          \post[Vptr mp] emp.
      #[global] Hint Opaque __addressof_spec : sl_opacity.
      #[global] Arguments __addressof_spec : simpl never.
      Definition __addressof_SpecFor := RegisterSpec __addressof_spec.
      #[global] Existing Instance __addressof_SpecFor.

      Definition addressof_spec :=
        specify.template.func "std::addressof" [Atype ty] (Tptr ty) [Tref ty] $
          \arg{mp} "" (Vref mp)
          \post[Vptr mp] emp.
      #[global] Hint Opaque addressof_spec : sl_opacity.
      #[global] Arguments addressof_spec : simpl never.
      Definition addressof_SpecFor := RegisterSpec addressof_spec.
      #[global] Existing Instance addressof_SpecFor.


    End with_ty.
  End with_cpp.
NES.End memory.
