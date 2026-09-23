(** Copying a shared handle only reads that handle. This client regression
    keeps its ownership fractional and checks that destroying the new copy
    returns the payload-acquisition token. It assumes the library operations;
    it does not verify libstdc++'s atomic reference-count implementation. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.invariants.
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
  #[local] Instance learn_shared : LearnEq6 SharedPtrR :=
    ltac:(solve_learnable).

  cpp.spec "copy_then_destroy(const std::shared_ptr<int>&)"
    from source as copy_then_destroy_spec with (
      \arg{other : ptr} "source" (Vref other)
      \prepost{q id source_pieceid p Rpiece}
        other |-> SharedPtrR "int" q id source_pieceid Rpiece p
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

  (* A destruction capability may recover its payload from an invariant.
     This is the pointwise obligation in [payload_destructible], not a rule
     turning arbitrary class bytes into a valid destructor precondition. *)
  Lemma guarded_int_destroy (p : ptr) (gamma : gname) :
    cinv nroot gamma (p |-> anyR "int" 1$m) ** cinv_own gamma 1
    |-- destroy_val (genv_tu σ) "int" p emp.
  Proof using MOD.
    rewrite <- fupd_destroy_val.
    eapply cinv_cancel_fwd with (P' := emp).
    { set_solver. }
    { go. }
    {
      rewrite <- fupd_destroy_val.
      apply timeless_unlater.
      { apply _. }
      etrans.
      2: { apply fupd_intro. }
      rewrite destroy_val_wp_destroy_val.
      go.
    }
  Qed.
End with_cpp.
