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

  Definition OS γ : Ostream :=
    AppHandler HelloWorld (⊤ ∖ ↑refinement_rootNS) masks.default γ.

  (* NOTE: the following two specializations work around issues with the
     Spectra packaging which uses bundling. *)
  Definition gen_X := gen_requester_C HelloWorld.
  Hint Resolve gen_X : sl_opacity.
  Definition bs_dos_steps_C :=
    gen_bs_dos_steps_C HelloWorld.(App.lts) HelloWorld.(App.inG).
  Hint Resolve bs_dos_steps_C : sl_opacity.


  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS γ) osM 1$m
    \persist Step.updater HelloWorld (⊤ ∖ ↑refinement_rootNS) γ
    \pre AuthSet.frag γ {[ "Hello World"%bs ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  (* Hint Resolve default_masks_valid : pure. *)
  Hint Extern 0 (masks.valid _ _) => (red; set_solver) : pure.

  Opaque ostream.bs_dos.

  Lemma main_ok : verify[source] "main()".
  Proof.
    #[local] Opaque ostream.bs_dos.
    verify_shift; go.
    banish_string_literals.
    iModIntro; go.
  Qed.

End with_cpp.
