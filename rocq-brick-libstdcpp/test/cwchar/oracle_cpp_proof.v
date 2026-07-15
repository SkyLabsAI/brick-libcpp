
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cwchar.spec.
Require Import skylabs.brick.libstdcpp.test.cwchar.oracle_cpp.
#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Section oracle_clients.
  Context `{Sigma : cpp_logic, sigma : genv, module ⊧ sigma}.

  cpp.spec "oracle_wcslen(const wchar_t*)" as oracle_wcslen_spec
      from module with
    (\arg{text_p} "text" (Vptr text_p)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require wcslen_callable (decode_wide_array raw)
     \require valid<"unsigned long"> (wcslen (decode_wide_array raw))
     \post[Vint (wcslen (decode_wide_array raw))] emp).

  Lemma oracle_wcslen_ok :
    verify[module] "oracle_wcslen(const wchar_t*)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcscmp(const wchar_t*, const wchar_t*)"
      as oracle_wcscmp_spec from module with
    (\arg{lhs_p} "lhs" (Vptr lhs_p)
     \arg{rhs_p} "rhs" (Vptr rhs_p)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require wcscmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs)
     \post[Vint (wcscmp (decode_wide_array lhs) (decode_wide_array rhs))] emp).

  Lemma oracle_wcscmp_ok :
    verify[module] "oracle_wcscmp(const wchar_t*, const wchar_t*)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q1, lhs, q2, rhs. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsncmp(const wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wcsncmp_spec from module with
    (\arg{lhs_p} "lhs" (Vptr lhs_p)
     \arg{rhs_p} "rhs" (Vptr rhs_p)
     \arg{count} "count" (Vint count)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require valid<"unsigned long"> count
     \require wcsncmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs) count
     \post[Vint (wcsncmp
       (decode_wide_array lhs) (decode_wide_array rhs) count)] emp).

  Lemma oracle_wcsncmp_ok :
    verify[module]
      "oracle_wcsncmp(const wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q1, lhs, q2, rhs. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcschr_const(const wchar_t*, wchar_t)"
      as oracle_wcschr_const_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require wcschr_callable (decode_wide_array raw) (Z.of_N target)
     \post[wide_search_result text_p
       (wcschr (decode_wide_array raw) (Z.of_N target))] emp).

  Lemma oracle_wcschr_const_ok :
    verify[module] "oracle_wcschr_const(const wchar_t*, wchar_t)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcschr_mutable(wchar_t*, wchar_t)"
      as oracle_wcschr_mutable_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require wcschr_callable (decode_wide_array raw) (Z.of_N target)
     \post[wide_search_result text_p
       (wcschr (decode_wide_array raw) (Z.of_N target))] emp).

  Lemma oracle_wcschr_mutable_ok :
    verify[module] "oracle_wcschr_mutable(wchar_t*, wchar_t)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsrchr_const(const wchar_t*, wchar_t)"
      as oracle_wcsrchr_const_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require wcsrchr_callable (decode_wide_array raw) (Z.of_N target)
     \post[wide_search_result text_p
       (wcsrchr (decode_wide_array raw) (Z.of_N target))] emp).

  Lemma oracle_wcsrchr_const_ok :
    verify[module] "oracle_wcsrchr_const(const wchar_t*, wchar_t)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsrchr_mutable(wchar_t*, wchar_t)"
      as oracle_wcsrchr_mutable_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require wcsrchr_callable (decode_wide_array raw) (Z.of_N target)
     \post[wide_search_result text_p
       (wcsrchr (decode_wide_array raw) (Z.of_N target))] emp).

  Lemma oracle_wcsrchr_mutable_ok :
    verify[module] "oracle_wcsrchr_mutable(wchar_t*, wchar_t)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemcmp(const wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wmemcmp_spec from module with
    (\arg{lhs_p} "lhs" (Vptr lhs_p)
     \arg{rhs_p} "rhs" (Vptr rhs_p)
     \arg{count} "count" (Vint count)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require valid<"unsigned long"> count
     \require wmemcmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs) count
     \post[Vint (wmemcmp
       (decode_wide_array lhs) (decode_wide_array rhs) count)] emp).

  Lemma oracle_wmemcmp_ok :
    verify[module]
      "oracle_wmemcmp(const wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q1, lhs, q2, rhs. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemchr_const(const wchar_t*, wchar_t, unsigned long)"
      as oracle_wmemchr_const_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \arg{count} "count" (Vint count)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require valid<"unsigned long"> count
     \require wmemchr_callable
       (decode_wide_array raw) (Z.of_N target) count
     \post[wide_search_result text_p
       (wmemchr (decode_wide_array raw) (Z.of_N target) count)] emp).

  Lemma oracle_wmemchr_const_ok :
    verify[module]
      "oracle_wmemchr_const(const wchar_t*, wchar_t, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemchr_mutable(wchar_t*, wchar_t, unsigned long)"
      as oracle_wmemchr_mutable_spec from module with
    (\arg{text_p} "text" (Vptr text_p)
     \arg{target} "target" (Vchar target)
     \arg{count} "count" (Vint count)
     \prepost{q raw} text_p |-> wide_arrayR q raw
     \require valid<"unsigned long"> count
     \require wmemchr_callable
       (decode_wide_array raw) (Z.of_N target) count
     \post[wide_search_result text_p
       (wmemchr (decode_wide_array raw) (Z.of_N target) count)] emp).

  Lemma oracle_wmemchr_mutable_ok :
    verify[module]
      "oracle_wmemchr_mutable(wchar_t*, wchar_t, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists q, raw. go $usenamed=true.
  Qed.

End oracle_clients.

(* Live-authored proofs for the <cwchar> oracle clients. *)
