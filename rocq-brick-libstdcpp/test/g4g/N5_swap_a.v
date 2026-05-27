Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N5_swap.
Require Import skylabs.brick.libstdcpp.test.g4g.N5_swap_a_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ behavior 2 3)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Swap : App.app := mkApp APP.
  Definition X := requester_C Swap.
  Hint Resolve X : sl_opacity.

  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do := Step.requester Swap E γ |}%I.
  Next Obligation. repeat intro. apply requester_ne; done. Qed.


  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS ⊤ γ) osM 1$m
    \pre AuthSet.frag γ {[ behavior 2 3 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

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


  Lemma main_ok : verify[source] "main()".
  Proof.
    (* TODO: this should be made more robust to not require this annotation *)
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro.
    work.
  Qed.
End with_cpp.

