Require Import skylabs.auto.cpp.proof.

(**
Temporary.
 *)

(* verify_spec diverges on templated specs,
but it works after [untemplate_goal] normalizes the name substitution with [vm_compute].
*)
Ltac untemplate_spec G :=
  let y := eval red in G in
  change G with y;
  rewrite /specify_notation.template_specify/specify_t;
  match goal with
  |- context [match ?y with _ => _ end] =>
    let z := eval vm_compute in y in
    change y with z
  end;
  cbn.

Ltac untemplate_goal :=
  match goal with
  |- _ ⊢ ?G =>
  untemplate_spec G
  end.

Ltac untemplate_bi :=
  match goal with
  |- ?S1 ⊣⊢ ?S2 =>
  untemplate_spec S1;
  untemplate_spec S2
  end.
