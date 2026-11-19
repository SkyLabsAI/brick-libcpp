(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.iris.extra.bi.linearity.
Require skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.mutex_trylock.trylock_cpp.source.
