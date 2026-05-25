Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N12_area_cpp.

Import linearity.

#[local] Open Scope Z_scope.

Definition area_of_rectangle (side1 side2 : Z) := side1 * side2.
Definition perimeter_of_rectangle (side1 side2 : Z) := 2 * (side1 + side2).

Definition behavior (side1 side2 : Z) : bs :=
  let newline : bs := "
"%bs in
  "Area = " ++ ostream.format_int (area_of_rectangle side1 side2) ++ newline ++ "Perimeter = " ++ ostream.format_int (perimeter_of_rectangle side1 side2).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Definition side1 := 5.
  Definition side2 := 6.

  #[local] Notation APP := (output_app (eq $ behavior side1 side2)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Area : App.app := mkApp APP.
  (* NOTE: Specializing this hint is necessary due to
     the current Spectra packaging *)
  Definition X := Step.requester Area.
  #[local] Hint Resolve X : sl_opacity.

  (* NOTE: generalizing this over an [App.app] is difficult because [App.app] hides
     the event signature. *)
  #[program]
  Definition OS (E : coPset) γ : Ostream :=
    {| do := Step.requester Area E γ |}%I.
  Next Obligation. intros. repeat intro. by apply requester_ne. Qed.

  #[program]
  Definition bs_dos_steps_C (s : bs) (s' : propset (Sts._state (App.lts Area))) str
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
    \pre AuthSet.frag γ {[ behavior side1 side2 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  cpp.spec "areaRectangle(int, int)" from source inline.
  cpp.spec "perimeterRectangle(int, int)" from source inline.

  Lemma main_ok : verify[source] "main()".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro.
    work.
  Qed.
End with_cpp.
