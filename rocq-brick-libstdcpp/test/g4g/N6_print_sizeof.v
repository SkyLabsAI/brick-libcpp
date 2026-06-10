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

  #[local] Abbreviation APP := (output_app (eq behavior)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance SizeOf : App.app := mkApp APP.
  #[program]
  Definition OS γ : Ostream :=
    AppHandler SizeOf (⊤ ∖ ↑refinement_rootNS) masks.default γ.

  (* NOTE: the following two specializations work around issues with the
     Spectra packaging which uses bundling. *)
  Definition gen_X := gen_requester_C SizeOf.
  Hint Resolve gen_X : sl_opacity.
  Definition bs_dos_steps_C :=
    gen_bs_dos_steps_C SizeOf.(App.lts) SizeOf.(App.inG).
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS γ) osM 1$m
    \persist Step.updater SizeOf (⊤ ∖ ↑refinement_rootNS) γ
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
