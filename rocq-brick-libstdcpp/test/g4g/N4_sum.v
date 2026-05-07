Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N4_sum_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ ostream.format_int 20)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Sum : App.app := mkApp APP.
  (* NOTE: Specializing this hint is necessary due to
     the current Spectra packaging *)
  Definition X := Step.requester Sum.
  #[local] Hint Resolve X : sl_opacity.


  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do evt K := Step.requester Sum E γ evt K |}%I.
  Next Obligation. repeat intro. apply requester_ne; done. Qed.

  #[program]
  Definition bs_dos_steps_C str (s s' : propset (Sts._state (App.lts Sum)))
    (ANY_STEPS : AnySteps only_output s ((fun x => Write x) <$> BS.string_to_bytes str) s') :=
    \cancelx
    \using{γ} AuthSet.frag γ s
    \proving{K : mpredI} ostream.bs_dos (OS ⊤ γ) str K
    \through (AuthSet.frag γ s' -∗ K)
    \end@{mpredI}.
  Next Obligation.
    simpl. clear.
    intros str s s' ANY_STEP.
    remember ((fun x => Write x) <$> BS.string_to_bytes str) as X.
    generalize dependent str.
    induction ANY_STEP; simpl.
    { destruct str; simpl; try congruence.
      intros. admit. }
    { destruct str; simpl; try congruence.
      inversion 1; subst; intros. admit.
    }
    { admit. }
  Admitted.
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS ⊤ γ) osM 1$m
    \pre AuthSet.frag γ {[ ostream.format_int 20 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  Lemma main_ok : verify[source] "main()".
  Proof. verify_spec; go. Qed.

End with_cpp.
