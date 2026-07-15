(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.

Require Export skylabs.brick.libstdcpp.cstdlib_intmath.pred.
Require Import skylabs.brick.libstdcpp.cstdlib_intmath.inc_cstdlib_intmath_cpp.

Section with_cpp.
  Context `{Sigma : cpp_logic, module ⊧ sigma}.

  (** Trivial destruction consumes a materialized [div_t]. *)
  cpp.spec "div_t::~div_t()" as div_t_dtor_spec with
    (\this this
     \pre{qr} this |-> div_tR 1$m qr
     \post emp).

  (** Trivial destruction consumes a materialized [ldiv_t]. *)
  cpp.spec "ldiv_t::~ldiv_t()" as ldiv_t_dtor_spec with
    (\this this
     \pre{qr} this |-> ldiv_tR 1$m qr
     \post emp).

  (** Trivial destruction consumes a materialized [lldiv_t]. *)
  cpp.spec "lldiv_t::~lldiv_t()" as lldiv_t_dtor_spec with
    (\this this
     \pre{qr} this |-> lldiv_tR 1$m qr
     \post emp).

End with_cpp.
