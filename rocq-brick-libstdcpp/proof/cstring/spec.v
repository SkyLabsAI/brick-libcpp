(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.lang.cpp.bi.split_cfrac.

Require Export skylabs.brick.libstdcpp.cstring.model.
Require Import skylabs.brick.libstdcpp.cstring.inc_cstring_cpp.

#[local] Set Primitive Projections.

#[local] Open Scope Z_scope.

Abbreviation search_result := (fun byte_ty p found =>
  Vptr (match found with
    | Some off => (p .[ byte_ty ! off ])
    | None => nullptr
    end)) (only parsing).

Definition same_sign (source dest : Z) : Prop :=
  match trichotomyT Z.lt source 0 with
  | inleft (left H) => dest < 0
  | inleft (right H) => dest = 0
  | inright H => dest > 0
  end.
#[global] Arguments same_sign !_ /.

Lemma same_sign_correct_lt s d :
  same_sign s d -> s < 0 <-> d < 0.
Proof. rewrite /same_sign; destruct trichotomyT as [[?|?]|?]; lia. Qed.
Lemma same_sign_correct_eq s d :
  same_sign s d -> s = 0 <-> d = 0.
Proof. rewrite /same_sign; destruct trichotomyT as [[?|?]|?]; lia. Qed.
Lemma same_sign_correct_gt s d :
  same_sign s d -> s > 0 <-> d > 0.
Proof. rewrite /same_sign; destruct trichotomyT as [[?|?]|?]; lia. Qed.

(* Keep complete C strings usable, and also accept readable bounded buffers. *)
mlock Definition strncmp_inputR `{Σ : cpp_logic} {σ : genv}
    q (terminated : bool) (s : bs) : Rep :=
  if terminated then cstring.R q s
  else nonnullR ** array_sliceR Tchar 0 (lengthZ (BS.string_to_bytes s))
    (fun b : N => charR q b) (BS.string_to_bytes s).

Section with_cpp.
Context `{Σ : cpp_logic, σ : genv}.

  #[global, program] Definition strncmp_cstring_C (p : ptr) q s q1 q2 :=
    \cancelx
    \consuming p |-> cstring.R q s
    \guard SplitCFrac q q1 q2
    \bound qq ss terminated
    \proving p |-> strncmp_inputR qq terminated ss
    \through [| qq = q1 |]
    \through [| ss = s |]
    \through [| terminated = true |]
    \deduce p |-> cstring.R q2 s
    \end@{mpred}.
  Next Obligation.
    intros; rewrite (split_cfrac q).
    rewrite (cfractional (P := fun cq => cstring.R cq s) q1 q2) _at_sep.
    iIntros "[H1 H2]". iFrame "H2".
    iIntros (qq ss terminated) "(-> & -> & ->)".
    rewrite strncmp_inputR.unlock. iExact "H1".
  Qed.

  #[global] Instance strncmp_array_cfractional hi bytes :
    CFractional (fun q => array_sliceR Tchar 0 hi
      (fun b : N => charR q b) bytes).
  Proof. rewrite array_sliceR.unlock. apply _. Qed.

  #[global, program] Definition strncmp_array_C
      (p : ptr) q hi bytes q1 q2
      (Hbytes : bytes =[Vm]=> BS.string_to_bytes (BS.bytes_to_string bytes)) :=
    \cancelx
    \consuming p |-> array_sliceR Tchar 0 hi (fun b : N => charR q b) bytes
    \guard SplitCFrac q q1 q2
    \bound qq ss terminated
    \proving p |-> strncmp_inputR qq terminated ss
    \through [| qq = q1 |]
    \through [| ss = BS.bytes_to_string bytes |]
    \through [| terminated = false |]
    (* Empty slices do not imply non-nullness. *)
    \through [| p <> nullptr |]
    \deduce p |-> array_sliceR Tchar 0 hi (fun b : N => charR q2 b) bytes
    \end@{mpred}.
  Next Obligation.
    intros; rewrite (split_cfrac q).
    rewrite (cfractional (P := fun cq => array_sliceR Tchar 0 hi
      (fun b : N => charR cq b) bytes) q1 q2) _at_sep.
    iIntros "[H1 H2]". iFrame "H2".
    iIntros (qq ss terminated) "(-> & -> & -> & %Hnonnull)".
    rewrite strncmp_inputR.unlock -(RedEq_eq Hbytes) _at_sep _at_nonnullR.
    iSplit; first by iPureIntro.
    iEval (rewrite array_sliceR.unlock _at_sep _at_only_provable) in "H1".
    iDestruct "H1" as "[_ Harray]".
    rewrite array_sliceR.unlock _at_sep _at_only_provable.
    iSplit; [by iPureIntro; lia | iExact "Harray"].
  Qed.

  (* Singleton arrays normalize to a character cell. *)
  #[global, program] Definition strncmp_char_C
      (p normalized_p : ptr) q (byte : N) q1 q2
      (Hbyte : [byte] =[Vm]=> BS.string_to_bytes (BS.bytes_to_string [byte])) :=
    \cancelx
    \consuming p |-> charR q byte
    \guard SplitCFrac q q1 q2
    \guard PtrNorm p normalized_p
    \bound qq ss terminated
    \proving normalized_p |-> strncmp_inputR qq terminated ss
    \through [| qq = q1 |]
    \through [| ss = BS.bytes_to_string [byte] |]
    \through [| terminated = false |]
    \deduce p |-> charR q2 byte
    \end@{mpred}.
  Next Obligation.
    intros; rewrite (_ptr_norm p normalized_p) (split_cfrac q).
    rewrite (cfractional (P := fun cq => charR cq byte) q1 q2) _at_sep.
    iIntros "[H1 H2]".
    iDestruct (observe (type_ptr Tchar normalized_p) with "H1") as "#?".
    iFrame "H2".
    iIntros (qq ss terminated) "(-> & -> & ->)".
    rewrite strncmp_inputR.unlock -(RedEq_eq Hbyte).
    rewrite array_sliceR.unlock /= arrayR_singleton
      !(_at_sep, _at_only_provable, _at_offsetR, _at_nonnullR).
    normalize_ptrs. iFrame "H1". work.
  Qed.

  Context `{source ⊧ σ}.

  cpp.spec "strlen" with
    (\arg{s_p} "__s" (Vptr s_p)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned long"> (cstring.strlen s)
     \post[Vint (cstring.strlen s)] emp).

  cpp.spec "strcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \prepost{q1 s1} s1_p |-> cstring.R q1 s1
     \prepost{q2 s2} s2_p |-> cstring.R q2 s2
     \post{res}[Vint res] [| same_sign (strcmp s1 s2) res |] ).

  cpp.spec "strncmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{n} "__n" (Vn n)
     \pre{q1 s1 terminated1} s1_p |-> strncmp_inputR q1 terminated1 s1
     \pre{q2 s2 terminated2} s2_p |-> strncmp_inputR q2 terminated2 s2
     \require terminated1 || strncmp_readable s1 n
     \require terminated2 || strncmp_readable s2 n
     \post{res}[Vint res]
       s1_p |-> (if terminated1 then cstring.R q1 s1
         else nonnullR ** array_sliceR Tchar 0 (lengthZ (BS.string_to_bytes s1))
           (fun b : N => charR q1 b) (BS.string_to_bytes s1)) **
       s2_p |-> (if terminated2 then cstring.R q2 s2
         else nonnullR ** array_sliceR Tchar 0 (lengthZ (BS.string_to_bytes s2))
           (fun b : N => charR q2 b) (BS.string_to_bytes s2)) **
       [| same_sign (strncmp s1 s2 n) res |] ).

  cpp.spec "strchr(char*, int)" as strchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \post[search_result Tchar s_p (strchr s (byte_of_int c))] emp).

  cpp.spec "strchr(const char*, int)" as strchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \post[search_result Tchar s_p (strchr s (byte_of_int c))] emp).

  cpp.spec "strrchr(char*, int)" as strrchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \post[search_result Tchar s_p (strrchr s (byte_of_int c))] emp).

  cpp.spec "strrchr(const char*, int)" as strrchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \post[search_result Tchar s_p (strrchr s (byte_of_int c))] emp).

  cpp.spec "strspn" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{accept_p} "__accept" (Vptr accept_p)
     \prepost{q s} s_p |-> cstring.R q s
     \prepost{accept_q accept} accept_p |-> cstring.R accept_q accept
     \require valid<"unsigned long"> (strspn s accept)
     \post[Vn (strspn s accept)] emp).

  cpp.spec "strcspn" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{reject_p} "__reject" (Vptr reject_p)
     \prepost{q s} s_p |-> cstring.R q s
     \prepost{reject_q reject} reject_p |-> cstring.R reject_q reject
     \require valid<"unsigned long"> (strcspn s reject)
     \post[Vn (strcspn s reject)] emp).

  cpp.spec "strpbrk(char*, const char*)" as strpbrk_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{accept_p} "__accept" (Vptr accept_p)
     \prepost{q s} s_p |-> cstring.R q s
     \prepost{accept_q accept} accept_p |-> cstring.R accept_q accept
     \post[search_result Tchar s_p (strpbrk s accept)] emp).

  cpp.spec "strpbrk(const char*, const char*)" as strpbrk_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{accept_p} "__accept" (Vptr accept_p)
     \prepost{q s} s_p |-> cstring.R q s
     \prepost{accept_q accept} accept_p |-> cstring.R accept_q accept
     \post[search_result Tchar s_p (strpbrk s accept)] emp).

  cpp.spec "strstr(char*, const char*)" as strstr_mut_spec with
    (\arg{haystack_p} "__haystack" (Vptr haystack_p)
     \arg{needle_p} "__needle" (Vptr needle_p)
     \prepost{haystack_q haystack} haystack_p |-> cstring.R haystack_q haystack
     \prepost{needle_q needle} needle_p |-> cstring.R needle_q needle
     \post[search_result Tchar haystack_p (strstr haystack needle)] emp).

  cpp.spec "strstr(const char*, const char*)" as strstr_const_spec with
    (\arg{haystack_p} "__haystack" (Vptr haystack_p)
     \arg{needle_p} "__needle" (Vptr needle_p)
     \prepost{haystack_q haystack} haystack_p |-> cstring.R haystack_q haystack
     \prepost{needle_q needle} needle_p |-> cstring.R needle_q needle
     \post[search_result Tchar haystack_p (strstr haystack needle)] emp).

(*  Strong but unsound before C++17, and awkward
  cpp.spec "memchr(void*, int, unsigned long)" as memchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \prepost{q hi bytes} s_p |-> array_sliceR Tuchar 0 hi
       (fun b : Z => ucharR q b) bytes
     \require match memchr bytes c with
              | Some off => True
              | None => (n <= hi)%Z
              end
     (*equivalently: \require hi >= n \/ (hi < n /\ exists off, memchr bytes c = Some off)*)
     \post[search_result Tuchar s_p
       (memchr (takeZ n bytes) c)] emp).

  cpp.spec "memchr(const void*, int, unsigned long)" as memchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \prepost{q hi bytes} s_p |-> array_sliceR Tuchar 0 hi
       (fun b : Z => ucharR q b) bytes
     \require match memchr bytes c with
              | Some off => True
              | None => (n <= hi)%Z
              end
     (*equivalently: \require hi >= n \/ (hi < n /\ exists off, memchr bytes c = Some off)*)
     \post[search_result Tuchar s_p
       (memchr (takeZ n bytes) c)] emp).
*)

(* All pointer arguments must be non-null, even when the length is
   0 ([cstring.syn] defers to C17 7.24.1p2; WG14 N3322 relaxes this only for
   C2y). Empty slices do not imply this, so the [mem*] specs below require it
   explicitly; the [str*] specs get it from [cstring.R]. *)

(* sound, but weak in C++17*)
   cpp.spec "memchr(void*, int, unsigned long)" as memchr_mut_simple_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \require s_p <> nullptr
     \prepost{q bytes} s_p |-> array_sliceR Tuchar 0 n (fun b : Z => ucharR q b) bytes
     \post[search_result Tuchar s_p (memchr bytes c)] emp).

  cpp.spec "memchr(const void*, int, unsigned long)" as memchr_const_simple_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \require s_p <> nullptr
     \prepost{q bytes} s_p |-> array_sliceR Tuchar 0 n (fun b : Z => ucharR q b) bytes
     \post[search_result Tuchar s_p (memchr bytes c)] emp).

  cpp.spec "memcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{z} "__n" (Vint z)
     \require s1_p <> nullptr
     \require s2_p <> nullptr
     \prepost{q1 bytes1} s1_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q1 b) bytes1
     \prepost{q2 bytes2} s2_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q2 b) bytes2
     \post{res}[Vint res] [| same_sign (memcmp bytes1 bytes2) res |] ).

  cpp.spec "memset" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{z} "__n" (Vint z)
     \require s_p <> nullptr
     \pre{l} s_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr s_p] s_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) (memset c z)).

  cpp.spec "memcpy" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{z} "__n" (Vint z)
     \require dest_p <> nullptr
     \require src_p <> nullptr
     \prepost{q bytes} src_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q b) bytes
     \pre{l} dest_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr dest_p] dest_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) bytes).

  (*Sound but weak: overlapping buffers not supported here*)
  cpp.spec "memmove" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{z} "__n" (Vint z)
     \require dest_p <> nullptr
     \require src_p <> nullptr
     \prepost{q bytes} src_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q b) bytes
     \pre{l} dest_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr dest_p] dest_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) bytes).

End with_cpp.

(* Let [go]/[work] supply either input representation to [strncmp]. *)
#[export] Hint Resolve strncmp_cstring_C strncmp_array_C strncmp_char_C : br_hints.
