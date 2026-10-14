(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.brick.libstdcpp.string.spec.
Require Import skylabs.brick.libstdcpp.test.string.test_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "SelfAssign(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as self_assign_spec with (
    \arg{p} "value" (Vref p)
    \prepost{s} p |-> basic_stringR "char" 1$m s
    \post emp).

  Lemma self_assign_ok : verify[source] self_assign_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "AssignAlias(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as assign_alias_spec with (
    \arg{p} "value" (Vref p)
    \prepost{s} p |-> basic_stringR "char" 1$m s
    \post emp).

  Lemma assign_alias_ok : verify[source] assign_alias_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "CopyAssign(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&, const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as copy_assign_spec with (
    \arg{dst} "destination" (Vref dst)
    \arg{src} "source" (Vref src)
    \pre{s} dst |-> basic_stringR "char" 1$m s
    \prepost{sourceShare otherS}
      if bool_decide (dst = src) then [| otherS = s /\ sourceShare = None |]
      else Exists q, [| sourceShare = Some q |] **
        src |-> basic_stringR "char" q otherS
    \post dst |-> basic_stringR "char" 1$m otherS).

  Lemma copy_assign_ok : verify[source] copy_assign_spec.
  Proof using MOD. verify_spec; case_bool_decide; go. Qed.

End with_cpp.
