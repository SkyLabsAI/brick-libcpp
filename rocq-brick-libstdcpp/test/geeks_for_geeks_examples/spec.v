Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.

(** TODO upstream *)
#[only(cfracsplittable)] derive cstring.R.

(** TODO upstream *)
#[global] Bind Scope bs_scope with cstring.t.
(* We only have `Bind Scope bs_scope with t.` inside `Module cstring.` *)

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.iostream_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter ostreamT : Type.
  Parameter ostreamR : cQp.t -> ostreamT -> Rep.
  Parameter ostream_contentR : cQp.t -> cstring.t -> Rep.

  #[global] Instance: LearnEqF1 ostreamR := ltac:(solve_learnable).
  #[global] Instance: LearnEqF1 ostream_contentR := ltac:(solve_learnable).

  cpp.spec "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char*)" from source as ostream_insert_spec with (
    \arg{osP} "" (Vptr osP)
    \prepost{osM} osP |-> ostreamR 1$m osM
    \pre{str} osP |-> ostream_contentR 1$m str
    \arg{strP} "" (Vptr strP)
    \prepost{q__s strM} strP |-> cstring.R q__s strM
    \post[Vptr osP]
      osP |-> ostream_contentR 1$m (str ++ strM)).

End with_cpp.
