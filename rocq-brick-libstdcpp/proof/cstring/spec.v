(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.

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

Section with_cpp.
Context `{Σ : cpp_logic, source ⊧ σ}.

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
     \prepost{q1 s1} s1_p |-> cstring.R q1 s1
     \prepost{q2 s2} s2_p |-> cstring.R q2 s2
     \post{res}[Vint res] [| same_sign (strncmp s1 s2 n) res |] ).

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

(* sound, but weak in C++17*)
   cpp.spec "memchr(void*, int, unsigned long)" as memchr_mut_simple_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \prepost{q bytes} s_p |-> array_sliceR Tuchar 0 n (fun b : Z => ucharR q b) bytes
     \post[search_result Tuchar s_p (memchr bytes c)] emp).

  cpp.spec "memchr(const void*, int, unsigned long)" as memchr_const_simple_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vint n)
     \prepost{q bytes} s_p |-> array_sliceR Tuchar 0 n (fun b : Z => ucharR q b) bytes
     \post[search_result Tuchar s_p (memchr bytes c)] emp).

  cpp.spec "memcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{z} "__n" (Vint z)
     \prepost{q1 bytes1} s1_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q1 b) bytes1
     \prepost{q2 bytes2} s2_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q2 b) bytes2
     \post{res}[Vint res] [| same_sign (memcmp bytes1 bytes2) res |] ).

  cpp.spec "memset" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{z} "__n" (Vint z)
     \pre{l} s_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr s_p] s_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) (memset c z)).

  cpp.spec "memcpy" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{z} "__n" (Vint z)
     \prepost{q bytes} src_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q b) bytes
     \pre{l} dest_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr dest_p] dest_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) bytes).

  (*Sound but weak: overlapping buffers not supported here*)
  cpp.spec "memmove" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{z} "__n" (Vint z)
     \prepost{q bytes} src_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR q b) bytes
     \pre{l} dest_p |-> array_sliceR Tuchar 0 z (fun _ : unit => anyR Tuchar 1$m) l (*(replicateZ z tt)*)
     \post[Vptr dest_p] dest_p |-> array_sliceR Tuchar 0 z (fun b : Z => ucharR 1$m b) bytes).

End with_cpp.
