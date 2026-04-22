(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.

Require Export skylabs.brick.libstdcpp.cstring.pred_old.
Require Import skylabs.brick.libstdcpp.cstring.inc_cstring_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  cpp.spec "strlen" with
    (\arg{s_p} "__s" (Vptr s_p)
     \prepost{q s tail} s_p |-> cstringz.R q s tail
     \require valid<"unsigned long"> (Z.of_N (strlen s))
     \post[Vn (strlen s)] emp).

  cpp.spec "strcmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \prepost{q1 s1 tail1} s1_p |-> cstringz.R q1 s1 tail1
     \prepost{q2 s2 tail2} s2_p |-> cstringz.R q2 s2 tail2
     \post[Vint (strcmp s1 s2)] emp).

  cpp.spec "strncmp" with
    (\arg{s1_p} "__s1" (Vptr s1_p)
     \arg{s2_p} "__s2" (Vptr s2_p)
     \arg{n} "__n" (Vn n)
     \prepost{q1 s1 tail1} s1_p |-> cstringz.R q1 s1 tail1
     \prepost{q2 s2 tail2} s2_p |-> cstringz.R q2 s2 tail2
     \post[Vint (strncmp s1 s2 n)] emp).
End with_cpp.
