(** Copying a shared handle only reads that handle. This client regression
    keeps its ownership fractional and checks that destroying the new copy
    returns the payload-acquisition token. It assumes the library operations;
    it does not verify libstdc++'s atomic reference-count implementation. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

#[elaborate]
cpp.prog source prog cpp:{{
#include <memory>
void copy_then_destroy(std::shared_ptr<int> const& source) {
    auto copy = source;
}
}}.

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : source ⊧ σ}.

  #[local] Hint Opaque SharedPtrR pieceRight : sl_opacity.
  #[local] Instance learn_shared : LearnEq5 SharedPtrR :=
    ltac:(solve_learnable).

  cpp.spec "copy_then_destroy(const std::shared_ptr<int>&)"
    from source as copy_then_destroy_spec with (
      \arg{other : ptr} "source" (Vref other)
      \prepost{q id p Rpiece}
        other |-> SharedPtrR "int" q id Rpiece p
      \prepost{pieceid} pieceRight id pieceid
      \pre [| (N.of_nat pieceid < N.pos maxContention)%N |]
      \post emp
    ).

  Lemma copy_then_destroy_ok : verify[source] copy_then_destroy_spec.
  Proof.
    verify_spec.
    go.
    iExists pieceid.
    go.
    iExists false, p, (id, pieceid), Rpiece.
    go.
  Qed.
End with_cpp.
