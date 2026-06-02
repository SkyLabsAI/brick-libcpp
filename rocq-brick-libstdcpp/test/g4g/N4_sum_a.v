Require Import skylabs.brick.libstdcpp.test.g4g.prelude.

Require Import skylabs.brick.libstdcpp.test.g4g.N4_sum_a_cpp.

Import linearity.

#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Notation APP := (output_app (eq $ ostream.format_int 20)).

  Context `{SPECTRA : !appG (output_app (eq $ ostream.format_int 20)) _Σ}.

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
