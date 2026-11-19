(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cerrno.spec.
Require Import skylabs.brick.libstdcpp.cstdlib.spec.
Require Import skylabs.brick.libstdcpp.test.cstdlib.calloc_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ} `{!HasStdThreads Σ}.

  (* The size overflows, so the only possible outcome is NULL with ENOMEM. *)
  cpp.spec "test_calloc_overflow()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post[Vbool true] errnoR th 1$m ENOMEM).
  Lemma test_calloc_overflow_ok : verify[source] "test_calloc_overflow()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

  (* The zero bytes are given back with [array_sliceR_ucharR_blockR]. *)
  cpp.spec "test_calloc_free()" with
    (\persist{th} current_thread th
     \pre{e} errnoR th 1$m e
     \post Exists e', errnoR th 1$m e').
  Lemma test_calloc_free_ok : verify[source] "test_calloc_free()".
  Proof. verify_spec; go; case_bool_decide; go. Qed.

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

    cpp.spec "test_calloc_zeroed()" with
      (\persist{th} current_thread th
       \pre{e} errnoR th 1$m e
       \post{r e'}[Vint r] errnoR th 1$m e' ** [| r = -1 \/ r = 0 |]%Z).
    Lemma test_calloc_zeroed_ok : verify[source] "test_calloc_zeroed()".
    Proof using MOD. verify_spec; go; case_bool_decide; go; iPureIntro; lia. Qed.
  End bytes.
End with_cpp.
