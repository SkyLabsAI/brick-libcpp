(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Stdlib.Strings.Byte.

Require Export skylabs.brick.libstdcpp.cctype.model.
Require Import skylabs.brick.libstdcpp.cctype.inc_cctype_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Notation EOF := (-1%Z) (only parsing).
#[local] mlock
Definition VALID {σ : genv} (c : Z) : Prop :=
  (valid<"unsigned char"> c \/ c = EOF).

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  (* TODO: these functions should be [extern "C"] and specified with
  [cpp.spec "isalpha" with], troubleshoot why this doesn't work on Mac. *)

  (** Determine if <i> represents <true> or <false>. *)
  #[local] Notation int_bool i b := (bool_decide (i <> 0) = b) (only parsing).

  cpp.spec (named "isalpha") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isalpha c) |]).

  cpp.spec (named "isdigit") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isdigit c) |]).

  cpp.spec (named "isalnum") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isalnum c) |]).

  cpp.spec (named "isspace") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isspace c) |]).

  cpp.spec (named "islower") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (islower c) |]).

  cpp.spec (named "isupper") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isupper c) |]).

  cpp.spec (named "isprint") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isprint c) |]).

  cpp.spec (named "ispunct") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (ispunct c) |]).

  cpp.spec (named "iscntrl") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (iscntrl c) |]).

  cpp.spec (named "isgraph") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isgraph c) |]).

  cpp.spec (named "isxdigit") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post{z}[Vint z] [| int_bool z (isxdigit c) |]).

  (* Specifications for Character Conversion Functions *)

  cpp.spec (named "tolower") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post[Vint (tolower c)] emp).

  cpp.spec (named "toupper") with
    (\arg{c} "c" (Vint c)
     \require VALID c
     \post[Vint (toupper c)] emp).

End with_cpp.

Require Import skylabs.auto.core.hints.
Lemma prove_valid {σ : genv} c :
  SolveArith (-1 <= c <= Evaluate (int_rank.max_val int_rank.Ichar Unsigned)) ->
  VALID c.
Proof.
  rewrite VALID.unlock.
  destruct (decide (c = -1)); eauto.
  destruct 1. left. Arith.arith_solve.
Qed.
#[global] Hint Resolve prove_valid : pure.
