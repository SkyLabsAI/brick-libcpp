Require Import skylabs.auto.cpp.proof.

(* TODO: upstream *)
#[global] Instance cfrac_scale_1 `{cpp_logic}:
  ∀ {A : Type} (R : cQp.t → A -> Rep) a (p : Qp),
    CFractional (λ q : cQp.t, R q a)
    → CFractional (λ q : cQp.t, R (cQp.scale p q) a).
Proof. by move=>* ??; rewrite cQp.scale_add_r. Qed.
