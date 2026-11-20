(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.cstdio.pred.
Require Export skylabs.brick.libstdcpp.iostream.spec.
Require Import skylabs.brick.libstdcpp.cstdio.inc_cstdio_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** <<fputs(s, stream)>> writes the bytes of the C string [s], without
      its terminator, to [stream] and returns a nonnegative value.

      Like the [<ostream>] insertion specs, this assumes the write succeeds:
      it does not cover the error case, where <<fputs>> returns <<EOF>>,
      sets the stream's error indicator and [errno]. *)
  cpp.spec "fputs" as fputs_spec with
    (\arg{s} "__s" (Vptr s)
     \arg{stream} "__stream" (Vptr stream)
     \prepost{OS γ} stream |-> cfile.R OS γ 1$m
     \prepost{q str} s |-> cstring.R q str
     \pre{Q} ostream.bs_dos OS str Q
     \post{r}[Vint r] [| 0 <= r |]%Z ** Q).
End with_cpp.
