(** Same-type copy assignment between distinct handles. This is an assumed
    library interface, not a verification of libstdc++'s reference counting.

    The source is nonempty; the destination may be empty. The old destination
    payload piece is required because assignment can destroy that payload.
    A fresh source slot is required before the old slot is refunded: libstdc++
    increments the new counter before releasing the old one. The source's
    own payload piece is neither required nor duplicated.

    Distinct handles sharing one control block are allowed. In that case the
    implementation leaves the counter unchanged; the logical transition
    exchanges the old destination piece for the requested available piece.
    Separating full destination ownership from source ownership excludes
    self-assignment. Empty sources and aliasing/custom-deleter shared_ptrs
    are outside this interface. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : inc_shared_ptr_cpp.source ⊧ σ}.
  Context (ty : type).
  #[local] Notation spty := ("std::shared_ptr".<< Atype ty >>)%cpp_name.

  Definition copy_assign :=
    specify.template.op spty OOEqual function_qualifiers.N
      (Tref (Tnamed spty)) [Tref (Tconst (Tnamed spty))] $
      \this this
      \arg{other : ptr} "other" (Vref other)
      \prepost{q id source_piece p Rpiece}
        other |-> SharedPtrR ty q id source_piece Rpiece p
      \pre{pieceid} pieceRight id pieceid
      \pre [| (N.of_nat pieceid < N.pos maxContention)%N |]
      \pre{(old_null : bool) old_id old_piece oldp oldR}
        if old_null then this |-> NullSharedPtrR ty 1$m
        else this |-> SharedPtrR ty 1$m old_id old_piece oldR oldp **
          oldp |-> oldR old_piece
      \post[Vref this]
        this |-> SharedPtrR ty 1$m id pieceid Rpiece p **
        p |-> Rpiece pieceid **
        if old_null then emp else pieceRight old_id old_piece.

  Definition SpecFor_copy_assign := RegisterSpec copy_assign.
  #[global] Existing Instance SpecFor_copy_assign.
End with_cpp.

#[global] Hint Opaque copy_assign : sl_opacity.
