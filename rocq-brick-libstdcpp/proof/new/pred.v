Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.auto.cpp.elpi.derive.bi.
Require Import skylabs.brick.libstdcpp.new.inc_new_cpp.
Require Export skylabs.brick.libstdcpp.new.model.
#[local] Set Primitive Projections.

cpp.enum "std::align_val_t" from source alias.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  (** The ownership of the allocator data structures.

   This would include ownership such as free lists and allocator data structures.
   In C++, these are generally ambient, so this is exposed as a predicate
   rather than a representation predicate.

   NOTE/TODO: The current interface exposes but does **not** use `allocatorP`,
   because doing so would effectively require
   threading this ownership everywhere which is not very ergonomic; however,
   formally, this makes the interface un-realizable.

   More investigation is needed to understand how to encapsulate this ownership
   (and other ownership like it). The most promising option to date is to use
   thread-local invariants, but this still introduces some level of verbosity.
   *)
  Parameter allocatorP : forall {σ : genv}, Qp -> mpred.
  #[only(fractional,fracvalid)] derive allocatorP.

  (** The allocation meta-data **owned by the allocator**.

      In a normal implementation of <<malloc>>, this is a few bytes before the
      returned pointer that stores meta data, e.g. the size of the allocation.

      [allocatedR q is_array alignment sz] also records the allocation form:
      [false] for <<operator new>> and [true] for <<operator new[]>>, and
      [None] for overloads without an alignment parameter or [Some al] for
      overloads passed [al]. Deallocation must match both, including the
      original alignment argument even when the address is more aligned.

      NOTE: While C++ often stores the size of the array next to a dynamically
      allocated array, the memory that backs this is **not** part of [allocatedR].
      That memory is owned by the C++ abstract machine.
   *)
  Parameter allocatedR : forall {σ : genv}, Qp -> bool -> option N -> N -> Rep.
  #[only(fractional,asfractional,fracvalid,timeless)] derive allocatedR.
  #[global] Instance: Cbn (Learn (any ==> learn_eq ==> learn_eq ==> learn_eq ==> learn_hints.fin) allocatedR).
  Proof. solve_learnable. Qed.

End with_cpp.

NES.Begin alloc.

  (** [tokenR_with_alignment ty alignment q] bundles the dynamic allocation
      token with its allocator resource, preserving the allocation overload's
      alignment argument. [tokenR ty q] covers allocation without that argument.
   *)
  sl.lock
  Definition tokenR_with_alignment `{Σ : cpp_logic} {σ : genv}
      (ty : type) (alignment : option N) (q : Qp) : Rep :=
    Exists storage_p overhead sz,
      [| size_of _ ty = Some sz |] **
      new_token.R q {| new_token.alloc_ty := ty ; new_token.storage_ptr := storage_p ; new_token.overhead := overhead |} **
      pureR (storage_p .[ "unsigned char" ! -overhead ] |-> allocatedR q (is_array_type ty) alignment (overhead + sz)).
  #[only(fractional,asfractional,fracvalid,timeless)] derive new_token.R.
  #[only(fracvalid,timeless)] derive tokenR_with_alignment.

  Abbreviation tokenR ty q := (tokenR_with_alignment ty None q) (only parsing).

  #[local] Open Scope string_scope. (* for IPM *)
  #[global] Instance tokenR_xxx `{Σ : cpp_logic} {σ : genv}
      (ty : type) (alignment : option N)
    : Fractional (tokenR_with_alignment ty alignment).
  Proof.
    rewrite tokenR_with_alignment.unlock.
    repeat first [ apply _
                 | apply fractional_exist; intros ].
    { apply observe_2_sep_l.
      apply observe_2_only_provable_impl.
      congruence. }
    { apply observe_2_exist; intros.
      apply observe_2_sep_r, observe_2_sep_l.
      iIntros "A B".
      iDestruct (observe_2 [| _ = _ |] with "A B") as "%".
      inversion H; eauto. }
    { do 2 (apply observe_2_exist; intros).
      apply observe_2_sep_r, observe_2_sep_l.
      iIntros "A B".
      iDestruct (observe_2 [| _ = _ |] with "A B") as "%".
      inversion H; eauto. }
  Qed.
  (* We should be able to derive this, but <<derive>> gets stuck trying to prove the above instance
  #[only(asfractional)] derive tokenR_with_alignment.
   *)

  #[global] Instance tokenR_asfractional `{Σ : cpp_logic} {σ : genv}
      (ty : type) (alignment : option N) (q : Qp) :
    AsFractional (tokenR_with_alignment ty alignment q)
      (tokenR_with_alignment ty alignment) q.
  Proof. solve_as_frac. Qed.
NES.End alloc.
