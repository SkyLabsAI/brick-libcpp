(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.

Require Export skylabs.brick.libstdcpp.cstdlib_intmath.lifecycle.
Require Import skylabs.brick.libstdcpp.cstdlib_intmath.inc_cstdlib_intmath_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  cpp.spec "abs" as abs_int_spec with
    (\arg{n} "__x" (Vint n)
     \require valid<"int"> (Z.abs n)
     \post[Vint (abs_int n)] emp).

  cpp.spec "std::abs(long)" as abs_long_spec with
    (\arg{n} "__i" (Vint n)
     \require valid<"long"> (Z.abs n)
     \post[Vint (abs_long n)] emp).

  cpp.spec "std::abs(long long)" as abs_long_long_spec with
    (\arg{n} "__x" (Vint n)
     \require valid<"long long"> (Z.abs n)
     \post[Vint (abs_long_long n)] emp).

  cpp.spec "labs" with
    (\arg{n} "__x" (Vint n)
     \require valid<"long"> (Z.abs n)
     \post[Vint (labs n)] emp).

  cpp.spec "llabs" with
    (\arg{n} "__x" (Vint n)
     \require valid<"long long"> (Z.abs n)
     \post[Vint (llabs n)] emp).

  cpp.spec "div" as div_int_spec with
    (\arg{numer} "__numer" (Vint numer)
     \arg{denom} "__denom" (Vint denom)
     \require denom <> 0 /\ valid<"int"> (Z.quot numer denom) /\
       valid<"int"> (Z.rem numer denom)
     \post{p}[Vptr p] p |-> div_tR 1$m (div_int numer denom)).

  cpp.spec "std::div(long, long)" as div_long_spec with
    (\arg{numer} "__i" (Vint numer)
     \arg{denom} "__j" (Vint denom)
     \require denom <> 0 /\ valid<"long"> (Z.quot numer denom) /\
       valid<"long"> (Z.rem numer denom)
     \post{p}[Vptr p] p |-> ldiv_tR 1$m (div_long numer denom)).

  cpp.spec "__gnu_cxx::div(long long, long long)" as div_long_long_spec with
    (\arg{numer} "__n" (Vint numer)
     \arg{denom} "__d" (Vint denom)
     \require denom <> 0 /\ valid<"long long"> (Z.quot numer denom) /\
       valid<"long long"> (Z.rem numer denom)
     \post{p}[Vptr p] p |-> lldiv_tR 1$m (div_long_long numer denom)).

  cpp.spec "ldiv" with
    (\arg{numer} "__numer" (Vint numer)
     \arg{denom} "__denom" (Vint denom)
     \require denom <> 0 /\ valid<"long"> (Z.quot numer denom) /\
       valid<"long"> (Z.rem numer denom)
     \post{p}[Vptr p] p |-> ldiv_tR 1$m (ldiv numer denom)).

  cpp.spec "lldiv" with
    (\arg{numer} "__numer" (Vint numer)
     \arg{denom} "__denom" (Vint denom)
     \require denom <> 0 /\ valid<"long long"> (Z.quot numer denom) /\
       valid<"long long"> (Z.rem numer denom)
     \post{p}[Vptr p] p |-> lldiv_tR 1$m (lldiv numer denom)).

End with_cpp.
