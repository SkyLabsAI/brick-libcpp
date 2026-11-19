(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cerrno.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.brick.libstdcpp.new.spec.
Require Import skylabs.brick.libstdcpp.test.cstdlib.free_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ} `{!HasStdThreads Σ}.

  cpp.spec "test_free_zero_size()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post Exists e', errnoR th 1$m e').
  Lemma test_free_zero_size_ok : verify[source] "test_free_zero_size()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  (* EINVAL is 22 on Linux. [free] leaves errno alone. *)
  cpp.spec "test_free_null()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post[Vint 22] errnoR th 1$m 22).
  Lemma test_free_null_ok : verify[source] "test_free_null()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_free_two_blocks()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post Exists e', errnoR th 1$m e').
  Lemma test_free_two_blocks_ok : verify[source] "test_free_two_blocks()".
  Proof. verify_spec; go; repeat (case_bool_decide; go). Qed.

  (* Memory from operator new cannot be given to free. If this ever
     verifies, [Fail Qed] rejects the test. *)
  Section new.
    Context `{alignment_support : !allocation_alignment_support σ}.
    cpp.spec "test_new_to_free()" with (\post emp).
    Lemma test_new_to_free_rejected : verify[source] "test_new_to_free()".
    Proof. verify_spec; go; case_bool_decide; go. Fail Qed. Abort.
  End new.

  (** Byte access to a block: view [blockR] as [anyR] bytes, and back. *)
  Section bytes.
    Lemma blockR_anyR_bytes (p : ptr) (n : N) q :
      p |-> blockR n q |--
      p |-> array_sliceR Tuchar 0 n (fun _ : unit => anyR Tuchar q) (replicateZ n ()).
    Proof. by rewrite blockR_equiv_array_sliceR. Qed.
    Lemma anyR_bytes_blockR (p : ptr) (n : N) q :
      p |-> array_sliceR Tuchar 0 n (fun _ : unit => anyR Tuchar q) (replicateZ n ()) |--
      p |-> blockR n q.
    Proof. by rewrite blockR_equiv_array_sliceR. Qed.
    Definition blockR_anyR_bytes_F := [FWD] blockR_anyR_bytes.
    Definition anyR_bytes_blockR_B := [BWD] anyR_bytes_blockR.
    #[local] Hint Resolve blockR_anyR_bytes_F anyR_bytes_blockR_B : sl_opacity.

    (* The written bytes are given back with [array_sliceR_ucharR_blockR]. *)
    cpp.spec "test_free_written()" with
      (\persist{th} current_thread th
       \pre{e} errnoR th 1$m e
       \post{r e'}[Vint r] errnoR th 1$m e' ** [| r = -1 \/ r = 16 |]%Z).
    Lemma test_free_written_ok : verify[source] "test_free_written()".
    Proof using MOD. verify_spec; go; case_bool_decide; go; iPureIntro; lia. Qed.
  End bytes.
End with_cpp.
