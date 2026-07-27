(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.brick.libstdcpp.optional.inc_optional_cpp.
Require Import skylabs.brick.libstdcpp.optional.inc_optional_cpp_templates.
Require Export skylabs.brick.libstdcpp.optional.pred.


Module inc_optional_cpp_concrete.
  (* libstdc++ 12 makes both specializations noexcept because unsigned char is nothrow-constructible from unsigned char& and unsigned char&&. *)
  Definition source : translation_unit :=
    let rvalue_ctor :=
      Build_Ctor "std::optional<unsigned char>"%cpp_name
        [("__t"%pstring, Trv_ref Tuchar)] CC_C Ar_Definite
        exception_spec.NoThrow None in
    let lvalue_ctor :=
      Build_Ctor "std::optional<unsigned char>"%cpp_name
        [("__t"%pstring, Tref Tuchar)] CC_C Ar_Definite
        exception_spec.NoThrow None in
    let symbols :=
      NM.add
        "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"%cpp_name
        (Oconstructor rvalue_ctor)
        (NM.add
          "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)"%cpp_name
          (Oconstructor lvalue_ctor)
          (symbols inc_optional_cpp.source)) in
    makeTranslationUnit
      symbols
      (types inc_optional_cpp.source)
      (namespace_aliases inc_optional_cpp.source)
      (initializer inc_optional_cpp.source)
      (asserts inc_optional_cpp.source)
      (abi inc_optional_cpp.source)
      (msymbols inc_optional_cpp.source)
      (mtypes inc_optional_cpp.source)
      (maliases inc_optional_cpp.source)
      (minstances inc_optional_cpp.source).

End inc_optional_cpp_concrete.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Let byte_ty : type := Tuchar.
  cpp.spec "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"
    as optional_uint8_value_rvalue_ctor_template_spec
    from inc_optional_cpp_concrete.source (
      \\with
      \this this
      \arg{src} "__t" (Vref src)
      \prepost{q b} src |-> ucharR q b
      \post Exists p,
        this |-> optional_uint8.R 1$m (Some b) (Some p)
    ).

  cpp.spec "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)"
    as optional_uint8_value_lvalue_ctor_template_spec
    from inc_optional_cpp_concrete.source (
      \\with
      \this this
      \arg{src} "__t" (Vref src)
      \prepost{q b} src |-> ucharR q b
      \post Exists p,
        this |-> optional_uint8.R 1$m (Some b) (Some p)
    ).


  cpp.spec "std::optional<$byte_ty>::optional(std::nullopt_t)"
    as optional_uint8_nullopt_ctor_template_spec
    from inc_optional_cpp.source
    templates inc_optional_cpp_templates.templates (
      \\with
      \this this
      \arg{tag} "" (Vptr tag)
      \post this |-> optional_uint8.R 1$m None None
    ).

  cpp.spec "std::optional<$byte_ty>::has_value() const"
    as optional_uint8_has_value_template_spec
    from inc_optional_cpp.source
    templates inc_optional_cpp_templates.templates (
      \\with
      \this this
      \prepost{q st contained}
        this |-> optional_uint8.R q st contained
      \post[Vbool (model.optional_uint8_model.has_value st)] emp
    ).

  cpp.spec "std::optional<$byte_ty>::operator*() const &"
    as optional_uint8_deref_const_lvalue_template_spec
    from inc_optional_cpp.source
    templates inc_optional_cpp_templates.templates (
      \\with
      \this this
      \prepost{q b p}
        this |-> optional_uint8.R q (Some b) (Some p)
      \post[Vref p] emp
    ).

  cpp.spec "std::optional<$byte_ty>::~optional()"
    as optional_uint8_destructor_template_spec
    from inc_optional_cpp.source
    templates inc_optional_cpp_templates.templates (
      \\with
      \this this
      \pre{st contained}
        this |-> optional_uint8.R 1$m st contained
      \post emp
    ).

  (** Materialize the remaining template-backed public payloads. *)
  Definition optional_uint8_value_lvalue_ctor_spec : mpred :=
    optional_uint8_value_lvalue_ctor_template_spec inc_optional_cpp.module.
  Definition optional_uint8_value_rvalue_ctor_spec : mpred :=
    optional_uint8_value_rvalue_ctor_template_spec inc_optional_cpp.module.
  Definition optional_uint8_nullopt_ctor_spec : mpred :=
    optional_uint8_nullopt_ctor_template_spec inc_optional_cpp.module.
  Definition optional_uint8_has_value_spec : mpred :=
    optional_uint8_has_value_template_spec inc_optional_cpp.module.
  Definition optional_uint8_deref_const_lvalue_spec : mpred :=
    optional_uint8_deref_const_lvalue_template_spec inc_optional_cpp.module.
  Definition optional_uint8_destructor_spec : mpred :=
    optional_uint8_destructor_template_spec inc_optional_cpp.module.

  #[global] Instance optional_uint8_value_lvalue_ctor_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_value_lvalue_ctor" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_value_lvalue_ctor"
      optional_uint8_value_lvalue_ctor_spec.

  #[global] Instance optional_uint8_value_rvalue_ctor_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_value_rvalue_ctor" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_value_rvalue_ctor"
      optional_uint8_value_rvalue_ctor_spec.

  #[global] Instance optional_uint8_nullopt_ctor_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_nullopt_ctor" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_nullopt_ctor"
      optional_uint8_nullopt_ctor_spec.

  #[global] Instance optional_uint8_has_value_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_has_value" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_has_value"
      optional_uint8_has_value_spec.

  #[global] Instance optional_uint8_deref_const_lvalue_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_deref_const_lvalue" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_deref_const_lvalue"
      optional_uint8_deref_const_lvalue_spec.

  #[global] Instance optional_uint8_destructor_spec_instance :
    SpecFor inc_optional_cpp.module
      "optional_uint8_destructor" :=
    SpecFor.mk inc_optional_cpp.module
      "optional_uint8_destructor"
      optional_uint8_destructor_spec.

End with_cpp.


