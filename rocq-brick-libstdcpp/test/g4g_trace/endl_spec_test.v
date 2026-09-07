(**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.brick.libstdcpp.iostream_trace.spec.

Example endl_content_is_line_feed :
  BS.string_to_bytes endl_content = [10%N] := eq_refl.
