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

  cpp.spec "FindChar(const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as find_char_spec with (
    \arg{p} "s" (Vref p)
    \prepost{q} p |-> basic_stringR "char" q "abca"
    \prepost{qn} string_npos_global qn
    \post[Vbool true] emp).

  Lemma find_char_ok : verify[source] find_char_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Append(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as append_spec with (
    \arg{p} "s" (Vref p)
    \pre{s} p |-> basic_stringR "char" 1$m s
    \post p |-> basic_stringR "char" 1$m (BS.append (BS.append s "a") "b")).

  Lemma append_ok : verify[source] append_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "EraseTail(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as erasetail_spec with (
    \arg{p} "s" (Vref p)
    \pre p |-> basic_stringR "char" 1$m "abc"
    \prepost{qn} string_npos_global qn
    \post p |-> basic_stringR "char" 1$m "a").

  Lemma erasetail_ok : verify[source] erasetail_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "EraseMiddle(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as erasemiddle_spec with (
    \arg{p} "s" (Vref p)
    \pre p |-> basic_stringR "char" 1$m "abc"
    \post p |-> basic_stringR "char" 1$m "ac").

  Lemma erasemiddle_ok : verify[source] erasemiddle_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "EraseAtEnd(std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as eraseatend_spec with (
    \arg{p} "s" (Vref p)
    \pre p |-> basic_stringR "char" 1$m "a"
    \prepost{qn} string_npos_global qn
    \post p |-> basic_stringR "char" 1$m "a").

  Lemma eraseatend_ok : verify[source] eraseatend_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "FindA(const std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>&)" as find_a_spec with (
    \arg{p} "s" (Vref p)
    \prepost{q s} p |-> basic_stringR "char" q s
    \post[Vn (match string_find (N_to_byte 97) 0 s with
               | Some i => N.of_nat i
               | None => N.ones 64
               end)] emp).

  Lemma find_a_ok : verify[source] find_a_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "FindInLocal()" as find_in_local_spec with (\post emp).

  Lemma find_in_local_ok : verify[source] find_in_local_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "FindInConstLocal()" as find_in_const_local_spec with (\post emp).

  Lemma find_in_const_local_ok : verify[source] find_in_const_local_spec.
  Proof using MOD. verify_spec; go. Qed.

End with_cpp.
