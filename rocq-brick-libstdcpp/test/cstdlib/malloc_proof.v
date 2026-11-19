(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cerrno.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.brick.libstdcpp.new.spec.
Require Import skylabs.brick.libstdcpp.test.cstdlib.malloc_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ} `{!HasStdThreads Σ}.

  (* On NULL, errno is ENOMEM. *)
  cpp.spec "test_malloc_errno()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post{e'}[Vbool true] errnoR th 1$m e').
  Lemma test_malloc_errno_ok : verify[source] "test_malloc_errno()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  (* Memory from malloc cannot be given to operator delete. If this ever
     verifies, [Fail Qed] rejects the test. *)
  cpp.spec "test_malloc_to_delete()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post Exists e', errnoR th 1$m e').
  Lemma test_malloc_to_delete_rejected : verify[source] "test_malloc_to_delete()".
  Proof. verify_spec; go; case_bool_decide; go. Fail Qed. Abort.

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

    cpp.spec "test_malloc_write_read()" with
      (\persist{th} current_thread th
       \pre{e} errnoR th 1$m e
       \post{r e'}[Vint r] errnoR th 1$m e' ** [| r = -1 \/ r = 16 |]%Z).
    Lemma test_malloc_write_read_ok : verify[source] "test_malloc_write_read()".
    Proof using MOD. verify_spec; go; case_bool_decide; go; iPureIntro; lia. Qed.

    (* 3 is only possible if the write to one block leaves the other alone. *)
    cpp.spec "test_malloc_two_blocks()" with
      (\persist{th} current_thread th
       \pre{e} errnoR th 1$m e
       \post{r e'}[Vint r] errnoR th 1$m e' ** [| r = -1 \/ r = 3 |]%Z).
    Lemma test_malloc_two_blocks_ok : verify[source] "test_malloc_two_blocks()".
    Proof using MOD.
      verify_spec; go; repeat (case_bool_decide; go).
      all: iPureIntro; lia.
    Qed.
  End bytes.
End with_cpp.
