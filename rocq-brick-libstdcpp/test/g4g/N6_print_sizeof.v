Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N6_print_sizeof_cpp.

Import linearity.

Definition newline := "
"%bs.

Definition behavior : bs :=
  "Size of int is: " ++ ostream.format_int 4 ++ newline ++
  "Size of char is: " ++ ostream.format_int 1 ++ newline ++
  "Size of float is: " ++ ostream.format_int 4 ++ newline ++
  "Size of double is: " ++ ostream.format_int 8 ++ newline.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq behavior)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance SizeOf : App.app := mkApp APP.
  Definition X := requester_C SizeOf.
  Hint Resolve X : sl_opacity.

  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do evt K := Step.requester SizeOf E γ evt K |}%I.
  Next Obligation. repeat intro. apply requester_ne; done. Qed.

  #[program]
  Definition bs_dos_steps_C (s : bs) (s' : propset (Sts._state (App.lts SizeOf))) str
    (ANY_STEPS : AnySteps only_output {[s]} ((fun x => Write x) <$> BS.string_to_bytes str) s') :=
    \cancelx
      \using{γ} AuthSet.frag γ {[s]}
      \proving{K : mpredI} ostream.bs_dos (OS:=OS ⊤ γ) str K
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
    \pre AuthSet.frag γ {[ behavior ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  Lemma main_ok : verify[source] "main()".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro.
    work.
  Qed.
End with_cpp.
