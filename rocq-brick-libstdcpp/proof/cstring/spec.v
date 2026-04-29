(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.

Require Export skylabs.brick.libstdcpp.cstring.pred.
Require Import skylabs.brick.libstdcpp.cstring.inc_cstring_cpp.

#[local] Set Primitive Projections.

#[local] Open Scope Z_scope.

Notation search_result p found :=
  match found with
  | Some 0 => Vptr p
  | Some off => Vptr (p .[ Tchar ! off ])
  | None => Vptr nullptr
  end (only parsing).

Notation byte_search_result byte_ty p found :=
  match found with
  | Some 0 => Vptr p
  | Some off => Vptr (p .[ byte_ty ! off ])
  | None => Vptr nullptr
  end (only parsing).

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  cpp.spec "strlen" with
    (\arg{s_p} "__s" (Vptr s_p)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned long"> (cstring.strlen s)
     \post[Vn (Z.to_N (cstring.strlen s))] emp).

  cpp.spec "strcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \prepost{q1 s1} s1_p |-> cstring.R q1 s1
     \prepost{q2 s2} s2_p |-> cstring.R q2 s2
     \post[Vint (strcmp s1 s2)] emp).

  cpp.spec "strncmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{n} "__n" (Vn n)
     \prepost{q1 s1} s1_p |-> cstring.R q1 s1
     \prepost{q2 s2} s2_p |-> cstring.R q2 s2
     \post[Vint (strncmp s1 s2 n)] emp).

  cpp.spec "strchr(char*, int)" as strchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned char"> c
     \post[search_result s_p (strchr s c)] emp).

  cpp.spec "strchr(const char*, int)" as strchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned char"> c
     \post[search_result s_p (strchr s c)] emp).

  cpp.spec "strrchr(char*, int)" as strrchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned char"> c
     \post[search_result s_p (strrchr s c)] emp).

  cpp.spec "strrchr(const char*, int)" as strrchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \prepost{q s} s_p |-> cstring.R q s
     \require valid<"unsigned char"> c
     \post[search_result s_p (strrchr s c)] emp).

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
     \post[search_result s_p (strpbrk s accept)] emp).

  cpp.spec "strpbrk(const char*, const char*)" as strpbrk_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{accept_p} "__accept" (Vptr accept_p)
     \prepost{q s} s_p |-> cstring.R q s
     \prepost{accept_q accept} accept_p |-> cstring.R accept_q accept
     \post[search_result s_p (strpbrk s accept)] emp).

  cpp.spec "strstr(char*, const char*)" as strstr_mut_spec with
    (\arg{haystack_p} "__haystack" (Vptr haystack_p)
     \arg{needle_p} "__needle" (Vptr needle_p)
     \prepost{haystack_q haystack} haystack_p |-> cstring.R haystack_q haystack
     \prepost{needle_q needle} needle_p |-> cstring.R needle_q needle
     \post[search_result haystack_p (strstr haystack needle)] emp).

  cpp.spec "strstr(const char*, const char*)" as strstr_const_spec with
    (\arg{haystack_p} "__haystack" (Vptr haystack_p)
     \arg{needle_p} "__needle" (Vptr needle_p)
     \prepost{haystack_q haystack} haystack_p |-> cstring.R haystack_q haystack
     \prepost{needle_q needle} needle_p |-> cstring.R needle_q needle
     \post[search_result haystack_p (strstr haystack needle)] emp).

(*
  Archived exact [unsigned char] array specs. These were useful for the first
  byte-array slice, but they are too narrow for the standard [void*] memory
  APIs, whose textual specifications operate on object bytes.

  cpp.spec "memchr(void*, int, unsigned long)" as memchr_mut_spec_old with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{k} "__n" (Vint k)
     \prepost{q n bytes} s_p |-> arrayLR Tuchar 0 n
       (fun b : Z => ucharR q b) bytes
     \require lengthZ bytes = Z.of_N n
     \post[byte_search_result s_p (memchr bytes c)] emp).

  cpp.spec "memchr(const void*, int, unsigned long)" as memchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vn n)
     \prepost{q bytes} s_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR q b) bytes
     \require lengthZ bytes = Z.of_N n
     \post[byte_search_result s_p (memchr bytes c)] emp).

  cpp.spec "memcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{n} "__n" (Vn n)
     \prepost{q1 bytes1} s1_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR q1 b) bytes1
     \prepost{q2 bytes2} s2_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR q2 b) bytes2
     \require lengthZ bytes1 = Z.of_N n
     \require lengthZ bytes2 = Z.of_N n
     \post[Vint (memcmp bytes1 bytes2)] emp).

  cpp.spec "memset" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vn n)
     \pre s_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun _ : unit => anyR Tuchar 1$m) (replicateZ (Z.of_N n) tt)
     \post[Vptr s_p] s_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR 1$m b) (memset c (Z.of_N n))).

  cpp.spec "memcpy" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{n} "__n" (Vn n)
     \prepost{q bytes} src_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR q b) bytes
     \pre dest_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun _ : unit => anyR Tuchar 1$m) (replicateZ (Z.of_N n) tt)
     \require lengthZ bytes = Z.of_N n
     \post[Vptr dest_p] dest_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR 1$m b) bytes).

  cpp.spec "memmove" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{n} "__n" (Vn n)
     \prepost{q bytes} src_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR q b) bytes
     \pre dest_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun _ : unit => anyR Tuchar 1$m) (replicateZ (Z.of_N n) tt)
     \require lengthZ bytes = Z.of_N n
     \post[Vptr dest_p] dest_p |-> arrayLR Tuchar 0 (Z.of_N n)
       (fun b : Z => ucharR 1$m b) bytes).
  *)

  cpp.spec "memchr(void*, int, unsigned long)" as memchr_mut_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vn n)
     \prepost{byte_ty q bytes} s_p |-> object_bytesR byte_ty q bytes
     \require lengthZ bytes = Z.of_N n
     \post[byte_search_result byte_ty s_p (memchr bytes c)] emp).

  cpp.spec "memchr(const void*, int, unsigned long)" as memchr_const_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vn n)
     \prepost{byte_ty q bytes} s_p |-> object_bytesR byte_ty q bytes
     \require lengthZ bytes = Z.of_N n
     \post[byte_search_result byte_ty s_p (memchr bytes c)] emp).

  cpp.spec "memcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{n} "__n" (Vn n)
     \prepost{byte_ty1 q1 bytes1} s1_p |->
       object_bytesR byte_ty1 q1 bytes1
     \prepost{byte_ty2 q2 bytes2} s2_p |->
       object_bytesR byte_ty2 q2 bytes2
     \require lengthZ bytes1 = Z.of_N n
     \require lengthZ bytes2 = Z.of_N n
     \post[Vint (memcmp bytes1 bytes2)] emp).

  cpp.spec "memset" with
    (\arg{s_p} "__s" (Vptr s_p)
     \arg{c} "__c" (Vint c)
     \arg{n} "__n" (Vn n)
     \pre{byte_ty} s_p |-> object_bytes_anyR byte_ty 1$m (Z.of_N n)
     \post[Vptr s_p] s_p |-> object_bytesR byte_ty 1$m
       (memset c (Z.of_N n))).

  cpp.spec "memcpy" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{n} "__n" (Vn n)
     \prepost{src_byte_ty q bytes} src_p |->
       object_bytesR src_byte_ty q bytes
     \pre{dest_byte_ty} dest_p |->
       object_bytes_anyR dest_byte_ty 1$m (Z.of_N n)
     \require lengthZ bytes = Z.of_N n
     \post[Vptr dest_p] dest_p |-> object_bytesR dest_byte_ty 1$m
       bytes).

  cpp.spec "memmove" with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{n} "__n" (Vn n)
     \prepost{src_byte_ty q bytes} src_p |->
       object_bytesR src_byte_ty q bytes
     \pre{dest_byte_ty} dest_p |->
       object_bytes_anyR dest_byte_ty 1$m (Z.of_N n)
     \require lengthZ bytes = Z.of_N n
     \post[Vptr dest_p] dest_p |-> object_bytesR dest_byte_ty 1$m
       bytes).
End with_cpp.
