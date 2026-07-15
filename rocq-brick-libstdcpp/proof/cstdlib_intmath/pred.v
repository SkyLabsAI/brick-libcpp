(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.cstdlib_intmath.model.

(** Canonical representation of the named fields of [div_t]. *)
mlock Definition div_tR `{Σ : cpp_logic} {σ : genv}
    (q : cQp.t) (qr : Z * Z) : Rep :=
  _field "div_t::quot" |-> primR "int" q (Vint qr.1)
  ** _field "div_t::rem" |-> primR "int" q (Vint qr.2)
  ** structR "div_t" q.

(** Canonical representation of the named fields of [ldiv_t]. *)
mlock Definition ldiv_tR `{Σ : cpp_logic} {σ : genv}
    (q : cQp.t) (qr : Z * Z) : Rep :=
  _field "ldiv_t::quot" |-> primR "long" q (Vint qr.1)
  ** _field "ldiv_t::rem" |-> primR "long" q (Vint qr.2)
  ** structR "ldiv_t" q.

(** Canonical representation of the named fields of [lldiv_t]. *)
mlock Definition lldiv_tR `{Σ : cpp_logic} {σ : genv}
    (q : cQp.t) (qr : Z * Z) : Rep :=
  _field "lldiv_t::quot" |-> primR "long long" q (Vint qr.1)
  ** _field "lldiv_t::rem" |-> primR "long long" q (Vint qr.2)
  ** structR "lldiv_t" q.

#[only(cfracsplittable)] derive div_tR.
#[only(cfracsplittable)] derive ldiv_tR.
#[only(cfracsplittable)] derive lldiv_tR.
#[only(lazy_unfold)] derive div_tR.
#[only(lazy_unfold)] derive ldiv_tR.
#[only(lazy_unfold)] derive lldiv_tR.
