(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.iris.extra.bi.linearity.
Require skylabs.brick.libstdcpp.test.pthread.join.join_cpp.

#[local] Abbreviation source :=
  skylabs.brick.libstdcpp.test.pthread.join.join_cpp.source.

NES.Begin join_message.
  cpp.class "join_message" prefix "" from source
    dataclass { default_specs }.
NES.End join_message.
