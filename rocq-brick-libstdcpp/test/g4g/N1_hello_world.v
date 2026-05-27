Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.iris.extra.base_logic.lib.spectra.

Require Import skylabs.brick.libstdcpp.test.g4g.prelude.

Require Import skylabs.brick.libstdcpp.test.g4g.N1_hello_world_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq "Hello World"%bs)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance HelloWorld : App.app := mkApp APP.
  Definition X := requester_C HelloWorld.
  Hint Resolve X : sl_opacity.

  (* NOTE: generalizing this over an [App.app] is difficult because [App.app] hides
     the event signature. *)
  #[program]
  Definition OS (E : coPset) γ : Ostream :=
  {| do := Step.requester HelloWorld E γ |}%I.
  Next Obligation. intros. repeat intro. by apply requester_ne. Qed.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS ⊤ γ) osM 1$m
    \pre AuthSet.frag γ {[ "Hello World"%bs ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).


  Lemma main_ok : verify[source] "main()".
  Proof. verify_shift; go. banish_string_literals. iModIntro; go. Qed.

End with_cpp.
