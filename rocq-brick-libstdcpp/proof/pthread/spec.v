(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.inc_hpp.

Require Export skylabs.bi.tls_modalities.

Require Import skylabs.auto.cpp.prelude.spec.

Module pthread_attr.
  Export pthread_attr.

  cpp.spec "pthread_attr_t::pthread_attr_t()"
    from source
    as ctor_spec
    with ( \this this
           \post this |-> pthread_attr.R 1$m None ).

  cpp.spec "pthread_attr_t::~pthread_attr_t()"
    from source
    as dtor_spec
    with ( \this this
           \pre{x} this |-> pthread_attr.R 1$m x
           \post emp ).

  cpp.spec "pthread_attr_init"
    as init_spec
    from source
    with (\arg{pattr} "attr" (Vptr pattr)
          \pre{attr}    pattr |-> pthread_attr.R 1$m attr
          \post[Vint 0] pattr |-> pthread_attr.R 1$m (Some pthread_attr.default)).

  cpp.spec "pthread_attr_destroy"
    as destroy_spec
    from source
    with (\arg{pattr} "attr" (Vptr pattr)
          \pre{attr}    pattr |-> pthread_attr.R 1$m attr
          \post[Vint 0] ∃ x, pattr |-> pthread_attr.R 1$m x).

End pthread_attr.
