
Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.cwchar_copy.pred.
Require Import skylabs.brick.libstdcpp.cwchar_copy.inc_cwchar_copy_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Abbreviation wide_pointer := (fun base offset =>
  base .[ Twchar ! offset]) (only parsing).

Abbreviation optional_wide_pointer := (fun base offset =>
  match offset with
  | Some p => wide_pointer base p
  | None => nullptr
  end) (only parsing).

Section with_cpp.
  Context `{Sigma : cpp_logic, module ⊧ sigma}.

  cpp.spec "wcscpy" as wcscpy_spec with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require wcscpy_callable before dest src
     \post[Vptr dest_p] Exists after,
       [| wcscpy_step before dest src dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wcsncpy" as wcsncpy_spec with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{count} "__n" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wcsncpy_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wcsncpy_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wcscat" as wcscat_spec with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require wcscat_callable before dest src
     \post[Vptr dest_p] Exists after,
       [| wcscat_step before dest src dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wcsncat" as wcsncat_spec with
    (\arg{dest_p} "__dest" (Vptr dest_p)
     \arg{src_p} "__src" (Vptr src_p)
     \arg{count} "__n" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wcsncat_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wcsncat_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wmemcpy" as wmemcpy_spec with
    (\arg{dest_p} "__s1" (Vptr dest_p)
     \arg{src_p} "__s2" (Vptr src_p)
     \arg{count} "__n" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wmemcpy_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wmemcpy_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wmemmove" as wmemmove_spec with
    (\arg{dest_p} "__s1" (Vptr dest_p)
     \arg{src_p} "__s2" (Vptr src_p)
     \arg{count} "__n" (Vint count)
     \with (base : ptr) before dest src
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require src_p = wide_pointer base src
     \require valid<"unsigned long"> count
     \require wmemmove_callable before dest src count
     \post[Vptr dest_p] Exists after,
       [| wmemmove_step before dest src count dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wmemset" as wmemset_spec with
    (\arg{dest_p} "__s" (Vptr dest_p)
     \arg{value} "__c" (Vchar value)
     \arg{count} "__n" (Vint count)
     \with (base : ptr) before dest
     \pre base |-> wide_memoryR 1$m before
     \require dest_p = wide_pointer base dest
     \require valid<"unsigned long"> count
     \require wmemset_callable before dest (Z.of_N value) count
     \post[Vptr dest_p] Exists after,
       [| wmemset_step before dest (Z.of_N value) count dest after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wcscoll" as wcscoll_spec with
    (\arg{lhs_p} "__s1" (Vptr lhs_p)
     \arg{rhs_p} "__s2" (Vptr rhs_p)
     \with (base : ptr) before lhs rhs locale
     \pre base |-> wide_memoryR 1$m before
     \prepost current_collationR locale
     \require lhs_p = wide_pointer base lhs
     \require rhs_p = wide_pointer base rhs
     \require wcscoll_callable locale before lhs rhs
     \post{result}[Vint result] Exists after,
       [| wcscoll_flat_step locale before lhs rhs result after |] **
       base |-> wide_memoryR 1$m after).

  cpp.spec "wcsxfrm" as wcsxfrm_spec with
    (\arg{dest_p} "__s1" (Vptr dest_p)
     \arg{src_p} "__s2" (Vptr src_p)
     \arg{count} "__n" (Vint count)
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
End with_cpp.

