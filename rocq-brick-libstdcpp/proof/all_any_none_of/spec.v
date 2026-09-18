(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.all_any_none_of.hints.
Require Import skylabs.brick.libstdcpp.all_any_none_of.inc_all_any_none_of_cpp.

(* C++20 non-policy instantiations for const unsigned char* iterators and a
   bool(unsigned char) function pointer. The selected bytes are preserved.
   [test x = None] leaves that callback result unspecified. [I k] tracks
   separate predicate state and exposes at most [length xs] calls, without
   specifying visited positions, order, exact count, or short-circuiting. *)
NES.Open all_any_none_of.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "std::all_of<const unsigned char*, bool (*)(unsigned char)>(const unsigned char*, const unsigned char*, bool (*)(unsigned char))"
    as all_of_spec from inc_all_any_none_of_cpp.source with
    (\arg{first} "__first" (Vptr first)
     \with (n : Z)
     \arg "__last" (Vptr (first .[ Tuchar ! n ]))
     \arg{pred} "__pred" (Vptr pred)
     \prepost{q xs} first |-> array_sliceR Tuchar 0 n (fun x => ucharR q x) xs
     \with (test : Z -> option bool) (I : Z -> mpred)
     \prepost pred |-> cptrR (predicate_spec xs test I)
     \pre I 0%Z
     \post{r : bool}[Vbool r]
       Exists k : Z, [| (0 <= k <= lengthZ xs)%Z |] ** I k **
         match all_value test xs with
         | Some b => [| r = b |]
         | None => emp
         end).

  cpp.spec "std::any_of<const unsigned char*, bool (*)(unsigned char)>(const unsigned char*, const unsigned char*, bool (*)(unsigned char))"
    as any_of_spec from inc_all_any_none_of_cpp.source with
    (\arg{first} "__first" (Vptr first)
     \with (n : Z)
     \arg "__last" (Vptr (first .[ Tuchar ! n ]))
     \arg{pred} "__pred" (Vptr pred)
     \prepost{q xs} first |-> array_sliceR Tuchar 0 n (fun x => ucharR q x) xs
     \with (test : Z -> option bool) (I : Z -> mpred)
     \prepost pred |-> cptrR (predicate_spec xs test I)
     \pre I 0%Z
     \post{r : bool}[Vbool r]
       Exists k : Z, [| (0 <= k <= lengthZ xs)%Z |] ** I k **
         match any_value test xs with
         | Some b => [| r = b |]
         | None => emp
         end).

  cpp.spec "std::none_of<const unsigned char*, bool (*)(unsigned char)>(const unsigned char*, const unsigned char*, bool (*)(unsigned char))"
    as none_of_spec from inc_all_any_none_of_cpp.source with
    (\arg{first} "__first" (Vptr first)
     \with (n : Z)
     \arg "__last" (Vptr (first .[ Tuchar ! n ]))
     \arg{pred} "__pred" (Vptr pred)
     \prepost{q xs} first |-> array_sliceR Tuchar 0 n (fun x => ucharR q x) xs
     \with (test : Z -> option bool) (I : Z -> mpred)
     \prepost pred |-> cptrR (predicate_spec xs test I)
     \pre I 0%Z
     \post{r : bool}[Vbool r]
       Exists k : Z, [| (0 <= k <= lengthZ xs)%Z |] ** I k **
         match none_value test xs with
         | Some b => [| r = b |]
         | None => emp
         end).

  Definition specs := all_of_spec ** any_of_spec ** none_of_spec.
  #[global] Hint Opaque specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive specs.
End with_cpp.
