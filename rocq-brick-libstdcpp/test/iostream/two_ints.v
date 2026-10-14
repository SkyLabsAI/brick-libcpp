(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.iostream.spec.
Import istream.

(** * Two consecutive [int] extractions

    On the input "12-34 ", [second] returns -34 with libstdc++: the first
    extraction stops at '-' and leaves it in the stream, as the read-ahead of
    [istream.R]. *)
cpp.prog source flags "-std=c++20 -stdlib=libstdc++" prog cpp:{{
  #include <istream>
  int second(std::istream &in) {
    int a = 0, b = 0;
    in >> a;
    in >> b;
    return b;
  }
  int first(std::istream &in) {
    int a = 5;
    in >> a;
    return a;
  }
}}.

(** On the inputs "x" and "99999999999 ", [first] returns 0 and 2147483647
    with libstdc++, and the extraction sets [failbit]. *)

Definition chars (s : String.string) : list N :=
  Byte.to_N <$> String.list_byte_of_string s.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} (remaining : list N -> mpred).
  #[local] Abbreviation script := (istream.script remaining).

  cpp.spec "second(std::istream&)" from source as second_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{g} inp |-> istream.R script g [] 1$m
    \pre remaining (chars "12-34 ")
    \post{n}[Vint n] [| n = -34 |]%Z **
      ∃ g' buf, inp |-> istream.R script g' buf 1$m ** remaining []).

  cpp.spec "first(std::istream&)" from source as first_fail_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{g} inp |-> istream.R script g [] 1$m
    \pre remaining (chars "x")
    \post{n}[Vint n] [| n = 0 |]%Z ** remaining []).

  cpp.spec "first(std::istream&)" from source as first_big_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{g} inp |-> istream.R script g [] 1$m
    \pre remaining (chars "99999999999 ")
    \post{n}[Vint n] [| n = 2147483647 |]%Z ** remaining []).

  (** The first extraction reads "12-" and keeps '-' in the stream; the
      second starts from it and reads "34 ". *)
  Lemma second_ok : verify[source] second_spec.
  Proof. verify_spec; go. Qed.

  (** After a failed extraction, the caller continues with the stored value,
      without the stream. *)
  Lemma first_fail_ok : verify[source] first_fail_spec.
  Proof. verify_spec; go. Qed.

  Lemma first_big_ok : verify[source] first_big_spec.
  Proof. verify_spec; go. Qed.
End with_cpp.
