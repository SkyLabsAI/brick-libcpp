Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.cpp.string.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** TODO upstream *)
#[only(cfracsplittable)] derive cstring.R.

(** TODO upstream *)
Bind Scope bs_scope with cstring.t.
(* We only have `Bind Scope bs_scope with t.` inside `Module cstring.` *)

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N0_hello_world_cpp.

(* cpp.prog source prog cpp:{{

// #include <iostream>
#include <stdio.h>

int main() {
  // Printing the name
  puts("Anmol");
  // cout << "Anmol";
  return 0;
}
}}. *)

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter ostreamT : Type.
  Parameter ostreamR : cQp.t -> ostreamT -> Rep.
  Parameter ostream_contentR : cQp.t -> cstring.t -> Rep.
  Instance: LearnEqF1 ostreamR := ltac:(solve_learnable).
  Instance: LearnEqF1 ostream_contentR := ltac:(solve_learnable).

  cpp.spec "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char*)" from source as ostream_insert_spec with (
    \arg{osP} "" (Vptr osP)
    \prepost{osM} osP |-> ostreamR 1$m osM
    \pre{str} osP |-> ostream_contentR 1$m str
    \arg{strP} "" (Vptr strP)
    \prepost{q__s strM} strP |-> cstring.R q__s strM
    \post[Vptr osP]
      osP |-> ostream_contentR 1$m (str ++ strM)).

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m (str ++ "Anmol")).

  (* cpp.spec "puts" from source as puts_spec with (
    \arg{p} "" (Vptr p)
    \prepost{q s} p |-> cstring.R q s
    \post{n}[Vint n] emp). *)

  Lemma main_ok : verify?[source] main_spec.
  Proof.
    verify_spec; go.
  Qed.

End with_cpp.

(* #include <bits/stdc++.h> *)

(* cpp.prog source prog cpp:{{

#include <iostream>

using namespace std;

int main() {
  // Printing the name using cout object
  cout << "Anmol";
  return 0;
}
}}.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" as main_spec with
    (\post emp).


End with_cpp. *)
