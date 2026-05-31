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
  #[program]
  Definition OS γ : Ostream :=
    AppHandler Area (⊤ ∖ ↑refinement_rootNS) masks.default γ.

  (* NOTE: the following two specializations work around issues with the
     Spectra packaging which uses bundling. *)
  Definition gen_X := gen_requester_C Area.
  Hint Resolve gen_X : sl_opacity.
  Definition bs_dos_steps_C := gen_bs_dos_steps_C Area.(App.lts) Area.(App.inG).
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS γ) osM 1$m
    \persist Step.updater Area (⊤ ∖ ↑refinement_rootNS) γ
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
