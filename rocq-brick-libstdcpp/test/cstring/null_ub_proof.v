(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cstring.spec.

(** * The [mem*] specs reject null pointers, even for length 0

    Each lemma instantiates a spec with the arguments of the matching client in
    [null_ub.cpp] (where [buf] is any pointer) and shows that its precondition
    is unsatisfiable: [wp_specD PQ args K] is the precondition of [PQ] at [args]
    together with the wand from its postcondition to [K]. *)

(** [spec_wp f] is the [WpSpec] of [f] as a function of the argument list and
    the continuation. *)
#[local] Ltac spec_wp s :=
  let t := eval red in s in
  lazymatch t with specify _ ?PQ => exact (wp_specD PQ) end.
#[local] Abbreviation spec_wp s := ltac:(spec_wp s) (only parsing).

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[local] Ltac solve := intros; rewrite /wp_specD /=; go.

  Lemma memchr_null K :
    spec_wp memchr_mut_simple_spec [Vptr nullptr; Vint 97; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memchr_const_null K :
    spec_wp memchr_const_simple_spec [Vptr nullptr; Vint 97; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memcmp_null_lhs buf K :
    spec_wp memcmp_spec [Vptr nullptr; Vptr buf; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memcmp_null_rhs buf K :
    spec_wp memcmp_spec [Vptr buf; Vptr nullptr; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memset_null K :
    spec_wp memset_spec [Vptr nullptr; Vint 0; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memcpy_null_dest buf K :
    spec_wp memcpy_spec [Vptr nullptr; Vptr buf; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memcpy_null_src buf K :
    spec_wp memcpy_spec [Vptr buf; Vptr nullptr; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memmove_null_dest buf K :
    spec_wp memmove_spec [Vptr nullptr; Vptr buf; Vint 0] K |-- False.
  Proof. solve. Qed.

  Lemma memmove_null_src buf K :
    spec_wp memmove_spec [Vptr buf; Vptr nullptr; Vint 0] K |-- False.
  Proof. solve. Qed.

  (** [strncmp] also accepts bounded buffers, which carry [nonnullR]. *)
  Lemma strncmp_null_lhs buf K :
    spec_wp strncmp_spec [Vptr nullptr; Vptr buf; Vint 0] K |-- False.
  Proof. solve. rewrite strncmp_inputR.unlock. destruct bound1; go. Qed.

  Lemma strncmp_null_rhs buf K :
    spec_wp strncmp_spec [Vptr buf; Vptr nullptr; Vint 0] K |-- False.
  Proof. solve. rewrite strncmp_inputR.unlock. destruct bound2; go. Qed.

  (** The [str*] specs already rejected null pointers through [cstring.R]. *)
  Lemma strlen_null K :
    spec_wp strlen_spec [Vptr nullptr] K |-- False.
  Proof. solve. Qed.

End with_cpp.
