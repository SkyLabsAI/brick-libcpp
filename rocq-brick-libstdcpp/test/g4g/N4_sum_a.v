Require Import skylabs.brick.libstdcpp.test.g4g.prelude.

Require Import skylabs.brick.libstdcpp.test.g4g.N4_sum_a_cpp.

Import linearity.

#[local] Open Scope Z_scope.

Definition output_app (init : bs -> Prop) : LTS output_event :=
  {| Sts._state := bs
   ; Sts._init_state := init
   ; Sts._step := only_output |}.


Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{SPECTRA : !appG (output_app (eq $ ostream.format_int 20)) _Σ}.

  #[program]
  Instance Sum : App.app :=
    {| App.evt := output_event
    ; App.lts := output_app (eq $ ostream.format_int 20)
    ; App.inG := _
    |}.
  Next Obligation.
    unshelve eapply mpred_prop.mpred_has_usual_own. apply SPECTRA.
  Defined.

  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do evt K := Step.requester Sum E γ evt K |}%I.
  Next Obligation. repeat intro. apply requester_ne; done. Qed.

  Definition X := Step.requester Sum.
  #[local] Hint Resolve X : sl_opacity.

  #[program]
  Definition bs_dos_steps_C (s : bs) (s' : propset (Sts._state (App.lts Sum))) str
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
    \pre AuthSet.frag γ {[ ostream.format_int 20 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).


  Lemma main_ok : verify[source] main_spec.
  Proof.
    verify_spec; go.

    wp_for (fun ρ =>
      \pre{i1} _local ρ "i" |-> intR 1$m i1
      \pre _local ρ "a" |-> intR 1$m (11 + i1)
      \require 0 <= i1 <= 9
      \post* _local ρ "i" |-> anyR "int" 1$m
      \post* _local ρ "a" |-> intR 1$m 20
      \post emp
    ).

    go.
    wp_if; go.
    wp_for (fun ρ => emp); go.
  Qed.
End with_cpp.
