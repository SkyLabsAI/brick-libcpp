Require Import skylabs.brick.libstdcpp.test.g4g.prelude.
Require Import skylabs.brick.libstdcpp.test.g4g.N4_sum_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ ostream.format_int 20)).

  Context `{SPECTRA : !appG APP _Σ}.

  #[local] Instance Sum : App.app := mkApp APP.
  #[program]
  Definition OS γ : Ostream :=
    AppHandler Sum (⊤ ∖ ↑refinement_rootNS) masks.default γ.

  (* NOTE: the following two specializations work around issues with the
     Spectra packaging which uses bundling. *)
  Definition gen_X := gen_requester_C Sum.
  Hint Resolve gen_X : sl_opacity.
  Definition bs_dos_steps_C := gen_bs_dos_steps_C Sum.(App.lts) Sum.(App.inG).
  Hint Resolve bs_dos_steps_C : sl_opacity.

  cpp.spec "main()" from source as main_spec with (
    \prepost{γ osM} _global "std::cout" |-> ostream.R (OS γ) osM 1$m
    \persist Step.updater Sum (⊤ ∖ ↑refinement_rootNS) γ
    \pre AuthSet.frag γ {[ ostream.format_int 20 ]}
    \post[Vint 0]  AuthSet.frag γ {[ ""%bs ]}).

  Lemma main_ok : verify[source] "main()".
  Proof. verify_spec; go. Qed.

End with_cpp.
