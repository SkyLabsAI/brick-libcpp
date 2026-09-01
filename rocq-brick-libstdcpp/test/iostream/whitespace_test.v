(**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Example vertical_tab_is_whitespace : istream.is_ws 11%N = true := eq_refl.
Example form_feed_is_whitespace : istream.is_ws 12%N = true := eq_refl.
