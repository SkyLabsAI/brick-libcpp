(** Checks spec discovery, fractional source ownership, the returned reference,
    and old-piece refund. Library operation bodies remain assumed. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.shared_ptr.assignment.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

#[elaborate]
cpp.prog source prog cpp:{{
#include <memory>
std::shared_ptr<int>& assign(std::shared_ptr<int>& destination,
                             std::shared_ptr<int> const& source) {
    return destination = source;
}
}}.

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : source ⊧ σ}.
  #[local] Instance learn_shared : LearnEq6 SharedPtrR :=
    ltac:(solve_learnable).

  cpp.spec "assign(std::shared_ptr<int>&, const std::shared_ptr<int>&)"
    from source as assign_spec with (
      \arg{dest : ptr} "destination" (Vref dest)
      \arg{other : ptr} "source" (Vref other)
      \prepost{q id source_piece p Rpiece}
        other |-> SharedPtrR "int" q id source_piece Rpiece p
      \pre{pieceid} pieceRight id pieceid
      \pre [| (N.of_nat pieceid < N.pos maxContention)%N |]
      \pre{(old_null : bool) old_id old_piece oldp oldR}
        if old_null then dest |-> NullSharedPtrR "int" 1$m
        else dest |-> SharedPtrR "int" 1$m old_id old_piece oldR oldp **
          oldp |-> oldR old_piece
      \post[Vref dest]
        dest |-> SharedPtrR "int" 1$m id pieceid Rpiece p **
        p |-> Rpiece pieceid **
        if old_null then emp else pieceRight old_id old_piece
    ).

  Lemma assign_ok : verify[source] assign_spec.
  Proof using MOD.
    verify_spec.
    go.
    iExists pieceid, old_null, old_id, old_piece, oldp, oldR.
    go.
  Qed.
End with_cpp.
