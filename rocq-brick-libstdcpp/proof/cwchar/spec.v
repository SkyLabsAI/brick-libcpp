
Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.cwchar.pred.
Require Import skylabs.brick.libstdcpp.cwchar.inc_cwchar_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Abbreviation wide_search_result := (fun p found =>
  Vptr (match found with
        | Some off => p .[ Twchar ! off ]
        | None => nullptr
        end)) (only parsing).

Section with_cpp.
  Context `{Sigma : cpp_logic, module ⊧ sigma}.

  cpp.spec "wcslen" as wcslen_spec with
    (\arg{s_p} "__s" (Vptr s_p)
     \prepost{q raw} s_p |-> wide_arrayR q raw
     \require wcslen_callable (decode_wide_array raw)
     \require valid<"unsigned long"> (wcslen (decode_wide_array raw))
     \post[Vint (wcslen (decode_wide_array raw))] emp).

  cpp.spec "wcscmp" as wcscmp_spec with
    (\arg{lhs_p} "__s1" (Vptr lhs_p)
     \arg{rhs_p} "__s2" (Vptr rhs_p)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require wcscmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs)
     \post[Vint (wcscmp (decode_wide_array lhs) (decode_wide_array rhs))] emp).

  cpp.spec "wcsncmp" as wcsncmp_spec with
    (\arg{lhs_p} "__s1" (Vptr lhs_p)
     \arg{rhs_p} "__s2" (Vptr rhs_p)
     \arg{count} "__n" (Vint count)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require valid<"unsigned long"> count
     \require wcsncmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs) count
     \post[Vint (wcsncmp
       (decode_wide_array lhs) (decode_wide_array rhs) count)] emp).
cpp.spec "wcschr" as wcschr_const_spec with
  (\arg{s_p} "__wcs" (Vptr s_p)
   \arg{target} "__wc" (Vchar target)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require wcschr_callable (decode_wide_array raw) (Z.of_N target)
   \post[Vptr (match wcschr (decode_wide_array raw) (Z.of_N target) with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).

cpp.spec "std::wcschr(wchar_t*, wchar_t)" as wcschr_mutable_spec with
  (\arg{s_p} "__p" (Vptr s_p)
   \arg{target} "__c" (Vchar target)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require wcschr_callable (decode_wide_array raw) (Z.of_N target)
   \post[Vptr (match wcschr (decode_wide_array raw) (Z.of_N target) with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).

cpp.spec "wcsrchr" as wcsrchr_const_spec with
  (\arg{s_p} "__wcs" (Vptr s_p)
   \arg{target} "__wc" (Vchar target)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require wcsrchr_callable (decode_wide_array raw) (Z.of_N target)
   \post[Vptr (match wcsrchr (decode_wide_array raw) (Z.of_N target) with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).

cpp.spec "std::wcsrchr(wchar_t*, wchar_t)" as wcsrchr_mutable_spec with
  (\arg{s_p} "__p" (Vptr s_p)
   \arg{target} "__c" (Vchar target)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require wcsrchr_callable (decode_wide_array raw) (Z.of_N target)
   \post[Vptr (match wcsrchr (decode_wide_array raw) (Z.of_N target) with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).


  cpp.spec "wmemcmp" as wmemcmp_spec with
    (\arg{lhs_p} "__s1" (Vptr lhs_p)
     \arg{rhs_p} "__s2" (Vptr rhs_p)
     \arg{count} "__n" (Vint count)
     \prepost{q1 lhs} lhs_p |-> wide_arrayR q1 lhs
     \prepost{q2 rhs} rhs_p |-> wide_arrayR q2 rhs
     \require valid<"unsigned long"> count
     \require wmemcmp_callable
       (decode_wide_array lhs) (decode_wide_array rhs) count
     \post[Vint (wmemcmp
       (decode_wide_array lhs) (decode_wide_array rhs) count)] emp).
cpp.spec "wmemchr" as wmemchr_const_spec with
  (\arg{s_p} "__s" (Vptr s_p)
   \arg{target} "__c" (Vchar target)
   \arg{count} "__n" (Vint count)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require valid<"unsigned long"> count
   \require wmemchr_callable
     (decode_wide_array raw) (Z.of_N target) count
   \post[Vptr (match wmemchr
                  (decode_wide_array raw) (Z.of_N target) count with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).

cpp.spec "std::wmemchr(wchar_t*, wchar_t, unsigned long)"
    as wmemchr_mutable_spec with
  (\arg{s_p} "__p" (Vptr s_p)
   \arg{target} "__c" (Vchar target)
   \arg{count} "__n" (Vint count)
   \prepost{q raw} s_p |-> wide_arrayR q raw
   \require valid<"unsigned long"> count
   \require wmemchr_callable
     (decode_wide_array raw) (Z.of_N target) count
   \post[Vptr (match wmemchr
                  (decode_wide_array raw) (Z.of_N target) count with
               | Some off => s_p .[ Twchar ! off ]
               | None => nullptr
               end)] emp).


End with_cpp.
(* Seeded for live rocq-ed authoring. *)
