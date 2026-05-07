Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N5_swap_cpp.

Import linearity.

Definition behavior (a b : Z) : bs :=
  let newline : bs := "
"%bs in
  "Before swapping a = " ++
    ostream.format_int a ++ " , b = " ++ ostream.format_int b ++ newline ++
    "After swapping a = " ++ ostream.format_int b ++ " , b = " ++ ostream.format_int a ++ newline.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ behavior 2 3)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Swap : App.app := mkApp APP.
  Definition X := requester_C Swap.
  Hint Resolve X : sl_opacity.

  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do evt K := Step.requester Swap E γ evt K |}%I.
  Next Obligation. repeat intro. apply requester_ne; done. Qed.

  #[program]
  Definition bs_dos_steps_C (s : bs) (s' : propset (Sts._state (App.lts Swap))) str
    (ANY_STEPS : AnySteps only_output {[s]} ((fun x => Write x) <$> BS.string_to_bytes str) s') :=
    \cancelx
    \using{γ} AuthSet.frag γ {[s]}
    \proving{K : mpredI} ostream.bs_dos (OS ⊤ γ) str K
    \through (AuthSet.frag γ s' -∗ K)
    \end@{mpredI}.
  Next Obligation.
    simpl.
    intros.
    iIntros "F" (?) "K".
    rewrite /Step.requester.
  Admitted.
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS ⊤ γ) osM 1$m
    \pre AuthSet.frag γ {[ behavior 2 3 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  Lemma main_ok : verify[source] "main()".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro; go.
  Qed.
End with_cpp.
