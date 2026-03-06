(**
Tentative iostreams specs.

These are trace-based specifications, and there is a _wish_ to move to a
different style of specifications.

*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.iostream.inc_iostream_cpp.

(** TODO upstream START *)
#[only(cfracsplittable)] derive cstring.R.

(** TODO upstream *)
#[global] Bind Scope bs_scope with cstring.t.
(* We only have `Bind Scope bs_scope with t.` inside `Module cstring.` *)

(** TODO upstream to auto *)
#[global] Instance refine_bs_app' (str a b : BS.t) :
  Refine1 true true (str ++ a = str ++ b)%bs [a = b].
Proof. tac_refine. exact: (inj (BS.append str)). Qed.

(** TODO upstream END *)

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter ostreamT : Type.
  Parameter ostreamR : cQp.t -> ostreamT -> Rep.
  Parameter ostream_contentR : cQp.t -> cstring.t -> Rep.
  (* TODO: type_ptr *)
  #[only(cfracsplittable)] derive ostreamR.
  #[only(cfracsplittable)] derive ostream_contentR.

  #[global] Instance: LearnEqF1 ostreamR := ltac:(solve_learnable).
  #[global] Instance: LearnEqF1 ostream_contentR := ltac:(solve_learnable).

  Parameter istreamT : Type.
  Parameter istreamR : cQp.t -> istreamT -> Rep.
  #[only(cfracsplittable)] derive istreamR.
  #[global] Instance: LearnEqF1 istreamR := ltac:(solve_learnable).

  Lemma ostream_contentR_aggressive (os_p : ptr) q str str':
    os_p |-> ostream_contentR q str ⊢
    [| str = str' |] -∗
    os_p |-> ostream_contentR q str'.
  Proof. work. Qed.
  Definition ostream_contentR_aggressiveC := [CANCEL] ostream_contentR_aggressive.

End with_cpp.

#[export] Hint Resolve ostream_contentR_aggressiveC : br_hints.
