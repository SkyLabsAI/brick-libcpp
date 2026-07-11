(**
 * Copyright (C) 2025 SkyLabs AI, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.

Require Import skylabs.cpp.spec.concepts.

NES.Begin std.allocator_traits.

  Class IsAllocator `{Σ : cpp_logic,σ : genv} (ty : type) :=
    { size_type : type ;
      alloc_state : Set ;
      #[global] size_type_is_prim_int :: PrimVal size_type Z ;
      #[global] is_RepFor :: BundledRep ty alloc_state ;
    }.
  Arguments size_type {_ _ _ _} ty {_}.

NES.End std.allocator_traits.

NES.Begin std.allocator.
  NES.Open allocator_traits.

  #[global] Abbreviation N ty := (Ninst "std::allocator" [Atype ty]).
  #[global] Abbreviation T ty := (Tnamed (Ninst "std::allocator" [Atype ty])).
  sl.lock Definition R `{Σ : cpp_logic,σ : genv} (ty : type) (q : cQp.t) (_ : ()) : Rep :=
    structR (N ty) q.
  #[only(ascfractional,cfractional,cfracvalid,type_ptr)] derive R.

  #[global] Instance R_agree `{Σ : cpp_logic,σ : genv} ty q1 q2 a1 a2 : Observe2 [| a1 = a2 |] (R ty q1 a1) (R ty q2 a2).
  Proof. by destruct a1,a2; apply observe_2_intro_only_provable; iIntros "? ? !%". Qed.

  #[global] Instance R_HasRep `{Σ : cpp_logic,σ : genv} ty : BundledRep (T ty) () := {| objR := R ty |}.

  #[global] Instance is_allocator `{Σ : cpp_logic,σ : genv} (ty : type) : IsAllocator (T ty) :=
    {| size_type := "unsigned long" ;
       alloc_state := () |}.


  Section lifecycle.
    Context `{Σ : cpp_logic, σ : genv}.
    Context (ty : type).

    Definition default_ctor :=
      specify.template.ctor (N ty) [] $
        \this this
        \post this |-> R ty (cQp.m 1) ().
    #[global] Hint Opaque default_ctor : sl_opacity.
    #[global] Arguments default_ctor : simpl never.
    Definition SpecFor_default_ctor := RegisterSpec default_ctor.
    #[global] Existing Instance SpecFor_default_ctor.

    Definition dtor :=
      specify.template.dtor (N ty) $
        \this this
        \pre this |-> R ty (cQp.m 1) ()
        \post emp.
    #[global] Hint Opaque dtor : sl_opacity.
    #[global] Arguments dtor : simpl never.
    Definition SpecFor_dtor := RegisterSpec dtor.
    #[global] Existing Instance SpecFor_dtor.
  End lifecycle.
NES.End std.allocator.
