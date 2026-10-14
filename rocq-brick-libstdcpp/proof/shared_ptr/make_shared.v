(** The normal-return interface of the non-array std::make_shared<T>, using
    the C++20 construct_at interface for its initialization obligation.

    Construction is NOT an axiom saying that arbitrary payload ownership can
    be created. The caller supplies a spec for the actual construct_at<T,
    Args...> specialization, including its forwarded arguments and side
    effects. That obligation must be proved from the payload initialization,
    using the payload's constructor specs. In particular, a forwarding
    reference to a shared_ptr can cause a by-value constructor argument copy;
    its copy credit belongs in [before], not in a hidden assumption.

    This file specifies, but does not verify, libstdc++'s allocation and
    control-block implementation. Allocation failure is not excluded by a
    normal-return postcondition. Arrays, custom allocators/deleters, aliasing,
    weak_ptr, enable_shared_from_this, and make_shared_for_overwrite are outside
    this factory spec. The pure inheritance guard excludes the additional
    weak-handle initialization performed after constructing such a payload.
    The allocation representation still covers both array layouts; this file
    adds no array-factory spec. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".
Import linearity.

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : inc_shared_ptr_cpp.source ⊧ σ}.

  Definition make_shared_no_esft (ty : type) : Prop :=
    match erase_qualifiers ty with
    | Tnamed cls => forall path base,
        class_derives cls path -> base ∈ cls :: path ->
        forall pack,
          base <> Ninst "std::enable_shared_from_this" pack /\
          base <> Ninst "std::__enable_shared_from_this" pack
    | _ => True
    end.

  Lemma make_shared_no_esft_no_bases cls layout :
    glob_def σ cls = Some (Gstruct layout) -> layout.(s_bases) = [] ->
    (forall pack,
      cls <> Ninst "std::enable_shared_from_this" pack /\
      cls <> Ninst "std::__enable_shared_from_this" pack) ->
    make_shared_no_esft (Tnamed cls).
  Proof.
    intros Hlayout Hbases Hname path base Hpath Hin pack.
    inversion Hpath; subst.
    { apply elem_of_cons in Hin. destruct Hin as [-> | Hin].
      { apply Hname. }
      { inversion Hin. } }
    { match goal with
      | H : _ !! cls = Some (Gstruct ?st) |- _ =>
          change (glob_def σ cls = Some (Gstruct st)) in H;
          rewrite Hlayout in H; injection H as Heq; subst st
      end.
      match goal with
      | H : _ ∈ layout.(s_bases) |- _ => rewrite Hbases in H; inversion H
      end. }
  Qed.

  (** A construction obligation, not an assumed payload-constructor spec.
      The input is raw, sufficiently large and aligned storage, not a live T.
      Placement new may give the object a different logical pointer; keep
      [provides_storage] and its lifetime token rather than equating pointers.
      [after] includes source ownership and other constructor side effects. *)
  Definition make_shared_construction (ty : type) (args : list type)
      (values : list val) (Rpiece : nat -> Rep) (before after : mpred) : mpred :=
    specify.template.func "std::construct_at"
      [Atype ty; Apack (map Atype args)] (Tptr ty)
      (Tptr ty :: map (trv_ref QM) args) $
      \arg{storage : ptr} "__location" (Vptr storage)
      \args values
      \pre{size alignment}
        [| size_of σ ty = Some size /\ align_of ty = Some alignment |]
      \pre [| storage <> nullptr |]
      \pre storage |-> blockR size 1$m ** storage |-> alignedR alignment
      \pre before
      \post{p : ptr} [Vptr p]
        provides_storage storage p ty **
        p |-> new_token.R 1%Qp (new_token.mk ty storage 0) **
        p |-> ([∗ list] i ∈ allPieceIds, Rpiece i) ** after.

  (* Keep both parts of the function name as direct parameters for spec
     discovery. Neither inverse [map Atype] inference nor reduction of the
     reference-collapsing function in FindSpec is available. The checked
     equalities below enforce a type-only pack and correct forwarding refs. *)
  Definition make_shared_spec (ty : type) (pack : list temp_arg)
      (parameter_types : list type) : mpred :=
    let args := map (fun a => match a with Atype t => t | _ => Tvoid end) pack in
    specify.template.func "std::make_shared"
      [Atype ty; Apack pack]
      (Tnamed ("std::shared_ptr".<< Atype ty >>))
      parameter_types $
      \args{values : list val} values
      \pre [| pack = map Atype args |]
      \pre [| parameter_types = map (trv_ref QM) args |]
      \pre [| length values = length args |]
      \pre [| make_shared_no_esft ty |]
      \pre [| match erase_qualifiers ty with
               | Tarray _ _ | Tincomplete_array _ => False
               | _ => True
               end |]
      \pre{Rpiece before after}
        make_shared_construction ty args values Rpiece before after
      \pre before
      \pre payload_destructible ty Rpiece
      \post{retp : ptr} [Vptr retp]
        Exists (id : CtrlBlockId) (p : ptr),
          [| payload_type id = ty |] **
          retp |-> SharedPtrR ty 1$m id 0 Rpiece p **
          p |-> Rpiece 0%nat **
          ([∗ list] i ∈ allButFirstPieceId, pieceRight id i) ** after.

  Definition SpecFor_make_shared := RegisterSpec (@make_shared_spec).
  #[global] Existing Instance SpecFor_make_shared.
End with_cpp.

#[global] Hint Opaque make_shared_construction make_shared_spec : sl_opacity.
