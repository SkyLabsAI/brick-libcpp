Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N5_swap.
Require Import skylabs.brick.libstdcpp.test.g4g.N5_swap_a_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ behavior 2 3)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Swap : App.app := mkApp APP.
  #[program]
  Definition OS γ : Ostream :=
    AppHandler Swap (⊤ ∖ ↑refinement_rootNS) masks.default γ.

  (* NOTE: the following two specializations work around issues with the
     Spectra packaging which uses bundling. *)
  Definition gen_X := gen_requester_C Swap.
  Hint Resolve gen_X : sl_opacity.
  Definition bs_dos_steps_C := gen_bs_dos_steps_C Swap.(App.lts) Swap.(App.inG).
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS γ) osM 1$m
    \persist Step.updater Swap (⊤ ∖ ↑refinement_rootNS) γ
    \pre AuthSet.frag γ {[ behavior 2 3 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

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
