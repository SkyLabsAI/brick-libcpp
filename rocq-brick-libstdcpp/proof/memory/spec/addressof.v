Require Import skylabs.auto.cpp.spec.

Require Import skylabs.brick.libstdcpp.memory.inc_hpp.
Require Import skylabs.brick.libstdcpp.memory.inc_hpp_templates.

NES.Begin memory.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    Section with_ty.
      Context (ty : type).

      cpp.spec "std::__addressof<$ty>($ty&)" as __addressof_spec from inc_hpp.source templates inc_hpp_templates.templates (
        \\with
        \arg{mp} "" (Vref mp)
        \post[Vptr mp] emp
      ).

      cpp.spec "std::addressof<$ty>($ty&)" as addressof_spec from inc_hpp.source templates inc_hpp_templates.templates (
        \\with
        \arg{mp} "" (Vref mp)
        \post[Vptr mp] emp
      ).

    End with_ty.
  End with_cpp.
NES.End memory.
