(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.test.

Require Import skylabs.brick.libstdcpp.array.pred.
Require Import skylabs.brick.libstdcpp.test.array.laws_cpp.
(**
   Tests for the laws in <<array/pred.v>> and for <<operator==>>: each client
   below verifies with plain [go], no proof-specific hints.
 *)

(** ** A <<std::array>> as a dataclass field *)
NES.Begin Holder.
  cpp.class "Holder" prefix "" from source dataclass.
NES.End Holder.

(** The synthesized model of the field is the list of element models. *)
Check Holder.bytes : Holder.T -> list Z.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.
  #[local] Open Scope Z_scope.
  Import normalize.normalize_ptr.

  (** NOTE: stated over [Holder.Build_T bs t] rather than a model [m]: with the
      projection [Holder.bytes m] as the slice contents, [go] does not extract the
      [i]-th cell of the field's [array_sliceR]. *)
  cpp.spec "HolderByte(const Holder&, unsigned long)" as holder_byte_spec with
    (\arg{hp} "h" (Vref hp)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 16
     \prepost{q bs t} hp |-> Holder.R q (Holder.Build_T bs t)
     \post[Vint (bs !!! i)] emp).

  Lemma holder_byte_ok : verify[ source ] holder_byte_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** [cpp.spec … default] finds [std.array.R] through [RepFor]. *)
  cpp.spec "Eq(const std::array<unsigned char, 16ul>&, const std::array<unsigned char, 16ul>&)"
    as eq_default_spec default.

  (** ** A <<const std::array>> local

      [wp_make_const] after initialization and [wp_make_mutable] before
      destruction, by [array_sliceR_wp_const] and [R_wp_const_Vint]. *)
  cpp.spec "ConstLocal()" as const_local_spec with (\post[Vint 3] emp).

  Lemma const_local_ok : verify[ source ] const_local_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Value initialization, then a member call

      <<a{}>> leaves a [val]-indexed slice of zeroes; [array_sliceR_fold_Vint]
      turns it into the [std.array.R] that <<fill>> requires. *)
  cpp.spec "ZeroThenFill(unsigned char)" as zero_then_fill_spec with
    (\arg{v} "v" (Vint v) \post[Vint v] emp).

  Lemma zero_then_fill_ok : verify[ source ] zero_then_fill_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Comparisons *)
  cpp.spec "Eq(const std::array<unsigned char, 16ul>&, const std::array<unsigned char, 16ul>&)"
    as eq_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{bp} "b" (Vref bp)
     \prepost{qa xs} ap |-> std.array.R "unsigned char" 16 qa xs
     \prepost{qb ys} bp |-> std.array.R "unsigned char" 16 qb ys
     \post[Vbool (bool_decide (xs = ys))] emp).

  Lemma eq_ok : verify[ source ] eq_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Ne(const std::array<int, 3ul>&, const std::array<int, 3ul>&)" as ne_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{bp} "b" (Vref bp)
     \prepost{qa xs} ap |-> std.array.R "int" 3 qa xs
     \prepost{qb ys} bp |-> std.array.R "int" 3 qb ys
     \post[Vbool (negb (bool_decide (xs = ys)))] emp).

  Lemma ne_ok : verify[ source ] ne_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "main()" as main_spec with (\post[Vint 0] emp).

  Lemma main_ok : verify[ source ] main_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** The laws on their own *)

  (** The fold law as a hint, under an existential. *)
  Lemma fold_Vint_ex (p : ptr) :
    p |-> array_sliceR "unsigned char" 0 2 (primR "unsigned char" 1$m) [Vint 0; Vint 1]
    |-- Exists xs, p |-> array_sliceR "unsigned char" 0 2 (fun x => primR "unsigned char" 1$m (Vint x)) xs.
  Proof. go. Qed.
End with_cpp.
