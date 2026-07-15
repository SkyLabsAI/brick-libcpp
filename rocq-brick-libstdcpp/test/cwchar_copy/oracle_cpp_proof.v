
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cwchar_copy.spec.
Require Import skylabs.brick.libstdcpp.test.cwchar_copy.oracle_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Section oracle_clients.
  Context `{Sigma : cpp_logic, sigma : genv, module ⊧ sigma}.

  cpp.spec "oracle_wcscpy(wchar_t*, const wchar_t*)"
      as oracle_wcscpy_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require wcscpy_callable before dest src
     \post[Vptr dest_p] Exists after,
       [| wcscpy_step before dest src dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcscpy_ok :
    verify[module] "oracle_wcscpy(wchar_t*, const wchar_t*)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsncpy(wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wcsncpy_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wcsncpy_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wcsncpy_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcsncpy_ok :
    verify[module]
      "oracle_wcsncpy(wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcscat(wchar_t*, const wchar_t*)"
      as oracle_wcscat_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require wcscat_callable before dest src
     \post[Vptr dest_p] Exists after,
       [| wcscat_step before dest src dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcscat_ok :
    verify[module] "oracle_wcscat(wchar_t*, const wchar_t*)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsncat(wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wcsncat_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wcsncat_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wcsncat_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcsncat_ok :
    verify[module]
      "oracle_wcsncat(wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemcpy(wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wmemcpy_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wmemcpy_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wmemcpy_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wmemcpy_ok :
    verify[module]
      "oracle_wmemcpy(wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemmove(wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wmemmove_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wmemmove_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wmemmove_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wmemmove_ok :
    verify[module]
      "oracle_wmemmove(wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wmemset(wchar_t*, wchar_t, unsigned long)"
      as oracle_wmemset_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{value} "value" (Vchar value)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require valid<"unsigned long"> count
     \require wmemset_callable before dest (Z.of_N value) count
     \post[Vptr dest_p] Exists after,
       [| wmemset_step before dest (Z.of_N value) count dest after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wmemset_ok :
    verify[module] "oracle_wmemset(wchar_t*, wchar_t, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcscoll(const wchar_t*, const wchar_t*)"
      as oracle_wcscoll_spec from module with
    (\arg{lhs_p} "lhs" (Vptr lhs_p)
     \arg{rhs_p} "rhs" (Vptr rhs_p)
     \with (base : ptr) before lhs rhs locale
     \pre base |-> wide_memoryR 1$m before
     \prepost current_collationR locale
     \require lhs_p = wide_pointer base lhs
     \require rhs_p = wide_pointer base rhs
     \require wcscoll_callable locale before lhs rhs
     \post{result}[Vint result] Exists after,
       [| wcscoll_flat_step locale before lhs rhs result after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcscoll_ok :
    verify[module] "oracle_wcscoll(const wchar_t*, const wchar_t*)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, lhs, rhs, locale. go $usenamed=true.
    iExists t. go $usenamed=true.
  Qed.

  cpp.spec "oracle_wcsxfrm(wchar_t*, const wchar_t*, unsigned long)"
      as oracle_wcsxfrm_spec from module with
    (\arg{dest_p} "dest" (Vptr dest_p)
     \arg{src_p} "src" (Vptr src_p)
     \arg{count} "count" (Vint count)
     \with (base : ptr) before dest src locale
     \pre base |-> wide_memoryR 1$m before
     \prepost current_collationR locale
     \require dest_p = optional_wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wcsxfrm_callable locale before dest src count
     \post{result}[Vint result] Exists after,
       [| wcsxfrm_flat_step locale before dest src count result after |] **
       base |-> wide_memoryR 1$m after).

  Lemma oracle_wcsxfrm_ok :
    verify[module]
      "oracle_wcsxfrm(wchar_t*, const wchar_t*, unsigned long)".
  Proof.
    verify_spec; go $usenamed=true.
    iExists base, before, dest, src, locale. go $usenamed=true.
    iExists t. go $usenamed=true.
  Qed.
End oracle_clients.

