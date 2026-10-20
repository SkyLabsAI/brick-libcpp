(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.string.spec.

Require Import skylabs.brick.libstdcpp.test.string.erase_out_of_range_cpp.

(** * The [erase] spec rejects a [pos] past the end

    [erase_past_end] gets stuck on [2 <= 1]; see
    erase_out_of_range_proof.expected. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  cpp.spec "erase_past_end(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" from source as erase_past_end_spec with (
    \arg{p} "s" (Vref p)
    \prepost{qn} string_npos_global qn
    \pre p |-> basic_stringR "char" 1$m "a"
    \post p |-> basic_stringR "char" 1$m "a").
  Lemma erase_past_end_ok : verify[source] erase_past_end_spec.
  Proof. verify_spec; go. Show. Fail Qed. Abort.
End with_cpp.
