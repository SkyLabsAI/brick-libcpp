(** Specs of shared_ptr.
We do not cover interaction with weak_ptr or enable_shared_from_this.
Custom deleters, custom allocators, aliasing constructors, and
make_shared_for_overwrite are not supported by these specs.
The representation supports separate allocations and make_shared's combined
allocations, including arrays. See [SharedAllocationR]. The non-array factory
spec is in shared_ptr/make_shared.v; neither file proves the library bodies.
We cover the following usage:
- after dynamically allocating a new object (using new or new[]), it is (typicall immediately) passed to the init constructor of shared_ptr (spec in [init_ctor] below). At this time, the caller's proof needs to come up with [Rpiece: nat->Rep], defining how the ownership of this newly allocated object will be split between various shared_ptr objects that refer to it. They pass in all pieces and get back the 0th piece: [Rpiece 0] and tokens [pieceRight ctrlid 1 ... pieceRight ctrlid (maxContention-1)] which the clients can use to later obtain ownership of those [Rpiece]s by calling the copy constructor. The last argument of [pieceRight] is the piece id. The first argument, [ctrlid], identifies a single protection unit (payload object pointer) that is reference counted. "ctrl" comes from the implementation using a dynamically allocated "control block" which has an atomic counter to track how many times the copy constructor has been called minus the number of such objects that have already been destructed.
[maxContention] bounds the number of simultaneously live handles to one control
block. For the supported libstdc++ ABI it is [INT_MAX], not the pointer-sized
unsigned maximum; see the definition below.

Raw-pointer adoption requires [payload_deletable]: every payload piece,
together with the retained allocation token, must suffice for the whole
selected delete/delete[] operation. A trivial destructor is not enough:
class-specific operator delete may access external resources. Such resources
must be included in the pieces, rather than framed away. This applies even to
objects allocated by ::new and is distinct from a caller-supplied custom deleter.
[shared_ptr_delete_operator] checks the exported default-deleter body to find
the actual selected operation; it does not guess global operator delete.

The make_shared factory instead requires [payload_destructible]. Its interior
payload must be destroyed but must NOT be passed to delete. [payload_delete]
records the choice and allocation alignment in the control-block identity;
[payload_releasable] retains the corresponding persistent capability through
copies, assignment, and repartitioning. Neither capability is assumed as an
unconditional property of arbitrary payload predicates.

The pieces may not always be fractional ownerships of an object (e.g. int). For example, when the shared_ptr protects an array, it is common to have every piece own an index of the array, so that different shared_ptr objects can be used to write to different indices concurrently, e.g. here: https://github.com/category-labs/monad/blob/90f8b796061aeaf78a2943c45eae5303f6ff7900/category/execution/ethereum/execute_block.cpp#L233

- To gain confidence in the provability of these specs, we sketch a definition of [SharedPtrR]. The [inv] definition is the most tricky part of it: it stores all the [Rpiece] and [pieceRight] ownerships that need to be dished out later or to be used for deletion when the reference count goes to 0.
The proposed ownership-transfer argument uses sequentially consistent (SC)
invariant reasoning. It does not justify the actual libstdc++ acquire/release
operations or prove that adding barriers suffices. The C++ method specs remain
assumed; the checked ghost-state and client lemmas are not a verification of
libstdc++'s concurrent implementation. A weak-memory justification may require
a different SharedPtrR and ownership-transfer protocol.

- When calling the copy constructor, the caller's proof has to come up with their pieceid (< maxContention) and give up
[pieceRight ctrlid pieceid], which they only get back when the newly constructed object is deleted.
They get [Rpiece pieceid] in return: their piece of the ownership of the payload object.
The new handle records [pieceid], so its destructor must return that piece.
Identical fractional payload pieces are still interchangeable; their acquisition
indices are not. A fractional ghost token inside each handle witnesses that
its index is outstanding, even when ownership of the handle itself is split.
The control block id (representing the location of the atomic reference counter) remains the same.
The proof will atomically increment the counter to take out the Rpiece from the invariant.

- There is another Rep predicate: [NullSharedPtrR]: for the case when the shared ptr represents a dummy null ptr, e.g. after a move constructor transfers away the ownerships to a new object.

- The proved [redistributePayloadOwnership] in shared_ptr/redistribution.v can
change the payload partition when the caller owns every live handle and its
piece, plus every unused acquisition right. It requires equivalence of the
whole payload ownership, at least one live handle, and explicit Timeless and
WeaklyObjective conditions for the invariant migration. It returns a new ghost
control-block identity while retaining all physical addresses and the actual
reference count. The old, unconstrained admitted redistribution rule has been
replaced, not retained as an alternative interface.
A common pattern where this can be useful is when the thread that calls new needs to initialize the object after wrapping it in a shared_ptr but before sharing it with other concurrent threads. So until that event, it will have the exclusive ownership of the entire object (Rpiece n = emp for n>0, Rpiece 0= objR 1) and later, we redistribute with (Rpiece n => objR (1/N)).

*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.new_delete.
Set Default Goal Selector "!".
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.cpp.stdlib.atomic.spec.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.new.hints.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.
Require Import skylabs.brick.libstdcpp.shared_ptr.inc_shared_ptr_cpp.
Require Export skylabs.brick.libstdcpp.shared_ptr.layout.
Require Export skylabs.brick.libstdcpp.shared_ptr.allocation.
Require Export skylabs.brick.libstdcpp.shared_ptr.no_esft.
Require Import iris.algebra.excl.
Require Import iris.algebra.frac.

NES.Open std.atomic.

(* Preserve the names previously defined in this module. *)
Abbreviation SP_impl := layout.SP_impl.
Abbreviation SP_acc := layout.SP_acc.

Record CtrlBlockId : Set :=
  {
    pieceRightLocs: list gname; (* each stores a unit. N -> gname may be tricky for constructor proof *)
    pieceHandleLocs: list gname; (* Fractional outstanding-index witnesses. *)
    dataLoc: ptr;
    payload_type: type; (* Complete managed-object type, including array length.
                          Not necessarily the type of an independent allocation. *)
    payload_delete: option (name * option N);
    (* Some (operator, alignment): raw adoption, with the whole delete
       operation prepaid. None: in-place payload, destruction only. *)
  }.

#[local] Open Scope N_scope.
(** libstdc++ stores [_Sp_counted_base::_M_use_count] in [_Atomic_word], an
    alias of signed [int] on our target. The generated C++ AST records [Tint]
    for that field. [inc_shared_ptr.cpp] checks that [_Atomic_word] is [int]
    and has maximum value 2147483647. A 64-bit pointer does not imply a
    64-bit reference count.

    There are exactly [maxContention] piece indices, including index zero
    for the initial owner. Consuming an available [pieceRight] before a copy
    means at most [maxContention - 1] handles were outstanding; incrementing
    then remains within [INT_MAX]. Destruction returns that index, so the
    limit concerns simultaneous handles, not the lifetime number of copies.

    The previous admitted lower bound [2^32 <= maxContention] was incompatible
    with this signed 32-bit count. Fix the capacity instead of merely weakening
    that lower bound while leaving the actual maximum unconstrained. This is
    a correction of the assumed library interface, not a proof of libstdc++'s
    shared-pointer implementation. *)
(* [Opaque] alone does not block [vm_compute]. Seal the definition so clients
   cannot accidentally expand [seq 0 (Pos.to_nat maxContention)]. *)
mlock Definition maxContention : positive := 2147483647%positive.

Lemma maxContentionLb : 2^31 - 1 <= Npos maxContention.
Proof. rewrite maxContention.unlock. exact (N.le_refl _). Qed.

Lemma maxContention_fits_int : (0 < Z.pos maxContention < 2^31)%Z.
Proof. rewrite maxContention.unlock. split; reflexivity. Qed.

Definition maxContentionQp := pos_to_Qp maxContention.
Definition allPieceIds : list nat := (seq 0 (Pos.to_nat maxContention)).
Definition allButFirstPieceId := (seq 1 (Pos.to_nat maxContention -1 )).

Definition countLN {A : Type} (f : A -> bool) (l : list A) : N :=
  lengthN (filter f l).

(** Read the delete-expression selected by Clang in the default libstdc++
    disposal path. In particular, absence of a virtual destructor does NOT
    imply global operator delete. Reject missing/unrecognized bodies. *)
Definition shared_ptr_delete_operator (tu : translation_unit) (ty : type)
    : option name :=
  let '(nm, arr, ety, operand) :=
    match erase_qualifiers ty with
    | Tarray _ _ =>
        let ety := SP_element ty in
        ((Nscoped "std::__sp_array_delete"
          (Nop function_qualifiers.Nc OOCall [Tptr ety])).<<Atype ety>>,
         true, ety, Ecast Cl2r (Evar "__p" (Tptr ety)))
    | _ =>
        let cn := shared_control_name SeparateAllocation ty in
        (Nscoped cn (Nfunction function_qualifiers.N "_M_dispose" []),
         false, ty, Ecast Cl2r
           (Emember true (Ethis (Tptr (Tnamed cn)))
             (Nid "_M_ptr") false (Tptr ty)))
    end in
  match tu.(symbols) !! nm with
  | Some (Omethod m) =>
      match m.(m_body) with
      | Some (UserDefined (Sseq [Sexpr (Edelete arr' op operand' ety')])) =>
          if bool_decide (arr = arr' /\ ety = ety' /\ operand = operand')
          then Some op else None
      | _ => None
      end
  | _ => None
  end.

Section specs.
  Context `{Σ : cpp_logic, MOD:inc_shared_ptr_cpp.source ⊧ σ}.
  #[local] Existing Instance br.ghost.excl_inG.
  #[local] Existing Instance br.ghost.frac_inG.

  (* The capability may capture persistent destructor specs. [destroy_val]
     already admits an initial fancy update, so callers may cancel payload
     invariants before destroying the object. Final release must first close
     the reference-count invariant, then invoke this capability. The allocation
     token remains separate for the subsequent deallocation. *)
  Definition payload_destructible (ty : type) (Rpiece : nat -> Rep) : mpred :=
    □ (Forall p : ptr,
      p |-> ([∗ list] pieceid ∈ allPieceIds, Rpiece pieceid) -*
      destroy_val (genv_tu σ) ty p emp).

  (** The allocation token and every payload piece jointly fund the actual
      delete operation, including class-specific deallocation and its effects.
      Callers can put any required external resources in the pieces. *)
  Definition payload_deletable (ty : type) (op : name) (alignment : option N)
      (Rpiece : nat -> Rep) : mpred :=
    □ (Forall p : ptr,
      (p |-> ([∗ list] pieceid ∈ allPieceIds, Rpiece pieceid) **
       p |-> alloc.tokenR_with_alignment ty alignment 1%Qp) -*
      wp_delete_dispatch op ty p emp).

  Definition payload_releasable (id : CtrlBlockId) (Rpiece : nat -> Rep) : mpred :=
    match payload_delete id with
    | Some (op, alignment) =>
        (* Keep selection evidence in each handle: the allocation invariant
           alone does not distinguish different deallocation functions. *)
        [| exists tu : translation_unit,
             tu ⊧ σ /\
             shared_ptr_delete_operator tu (payload_type id) = Some op |] **
        payload_deletable (payload_type id) op alignment Rpiece
    | None => payload_destructible (payload_type id) Rpiece
    end.

  Definition payload_allocation (id : CtrlBlockId) (p : ptr) : mpred :=
    match payload_delete id with
    | Some (_, alignment) =>
        SharedAllocationR SeparateAllocation (payload_type id) alignment (dataLoc id) p
    | None =>
        SharedAllocationR CombinedAllocation (payload_type id) None (dataLoc id) p
    end.

  #[global] Instance payload_releasable_persistent id R :
    Persistent (payload_releasable id R).
  Proof.
    unfold payload_releasable.
    destruct (payload_delete id) as [[op alignment]|]; apply _.
  Qed.

  #[global] Instance payload_releasable_affine id R :
    Affine (payload_releasable id R).
  Proof.
    unfold payload_releasable.
    destruct (payload_delete id) as [[op alignment]|]; apply _.
  Qed.

  Section tty. Context (ty:type).

  Import linearity.


  (* just an exclusive token for each pieceid. can be defined with a simpler CMRA as fractionality is not needed. fgptsoQ has good automation support  *)
  Definition pieceRight ctrlid pieceid : mpred :=
    match nth_error (pieceRightLocs ctrlid) pieceid with
    | Some g => own (A := exclR unitO) g (Excl ())
    | None => emp (* bad argument, pieceid > maxContention *)
    end.

  #[global] Hint Opaque pieceRight : sl_opacity.

  (* The full token is in the invariant while this index is available, and in
     the handle while it is outstanding. Unlike [pieceRight], this token must
     split when a client shares read ownership of the same handle. *)
  Definition pieceHandle ctrlid (q : Qp) pieceid : mpred :=
    match nth_error (pieceHandleLocs ctrlid) pieceid with
    | Some g => own (A := fracR) g q
    | None => False
    end.

  #[global] Instance pieceHandle_fractional id i :
    Fractional (fun q => pieceHandle id q i).
  Proof.
    unfold pieceHandle.
    destruct (nth_error (pieceHandleLocs id) i) as [g |].
    { intros q1 q2. rewrite <- own_op. reflexivity. }
    { apply _. }
  Qed.

  Definition sptrInv (id: CtrlBlockId) (Rpiece : nat -> Rep) (ownedPtr:ptr) (pieceOut : nat ->bool) : mpred :=
    let ctrVal := countLN pieceOut allPieceIds in
    ([∗ list] pieceid ∈ allPieceIds,
               if pieceOut pieceid then pieceRight id pieceid
               else pieceHandle id 1 pieceid)
         ** (if (bool_decide (ctrVal = 0))
              then emp
              else (dataLoc id) .,
                     (SP_counted_base .:: Nid "_M_use_count")
                     |-> intR 1$m (Z.of_N ctrVal)
                    ** payload_allocation id ownedPtr
                    ** ([∗ list] pieceid ∈ allPieceIds,
                      if pieceOut pieceid then emp else ownedPtr |-> Rpiece pieceid)).

  (** [_M_use_count] is a raw [int] accessed by atomic builtins, not a
      [std::atomic<long>] subobject. The invariant protects its ownership.
      At the last release all physical resources leave this invariant: the
      releasing thread destroys the payload and frees the control block.
      The zero-count state retains only ghost tokens. A live handle excludes
      that state by [pieceHandle_live] in [handle_liveness.v]. This also
      permits closing the invariant before running a reentrant destructor.

      This remains a partial control-block model for the assumed library
      specs, not a verified libstdc++ implementation. It now retains the
      appropriate allocation ownership in [SharedAllocationR].
      A complete body proof must additionally own the remaining control-block
      fields and dynamic-class witnesses, account for its implicit weak
      reference, and justify the actual acquire/release operations. For an
      array factory it must also connect _M_n/_S_tail to the retained allocation
      size and recover the padding for deallocation. No external weak_ptr
      operations are covered by this interface. *)
  
  (** The control-block model above remains abstract. [SharedPtrHandleR]
      describes the complete handle, not the object its [_M_pi] points to. *)
  (* [q] describes this handle, not the shared control block or a payload
     piece. In particular, splitting [q] does not create a [pieceRight]. *)
  Definition SharedPtrR (q : cQp.t) (id: CtrlBlockId) (pieceid : nat)
      (Rpiece : nat -> Rep) (ownedPtr:ptr) : Rep :=
    SharedPtrHandleR ty q ownedPtr (dataLoc id)
    (* Managed-type compatibility alone is not permission to delete ownedPtr.
       The stable cleanup descriptor governs both the capability and allocation. *)
    ** [| delete_compat ty (payload_type id) |]
    ** pureR (payload_releasable id Rpiece)
    ** [| ownedPtr<>nullptr |] (* use NullSharedPtr otherwise *)
    ** [| lengthN (pieceRightLocs id) = Npos maxContention |]
    ** [| lengthN (pieceHandleLocs id) = Npos maxContention |]
    ** [| (N.of_nat pieceid < Npos maxContention)%N |]
    ** pureR (pieceHandle id (cQp.frac q) pieceid)
    ** pureR (inv nroot (Exists (pieceOut : nat ->bool), sptrInv id Rpiece ownedPtr pieceOut)).

  Definition NullSharedPtrR (q : cQp.t) : Rep :=
    SharedPtrHandleR ty q nullptr nullptr.

  #[global] Instance SharedPtrR_fractional id i Rpiece p :
    CFractional (fun q => SharedPtrR q id i Rpiece p) := _.
  #[global] Instance SharedPtrR_as_fractional q id i Rpiece p :
    AsCFractional (SharedPtrR q id i Rpiece p)
      (fun q => SharedPtrR q id i Rpiece p) q.
  Proof. split; [done | apply _]. Qed.
  #[global] Instance NullSharedPtrR_fractional :
    CFractional NullSharedPtrR := _.
  #[global] Instance NullSharedPtrR_as_fractional q :
    AsCFractional (NullSharedPtrR q) NullSharedPtrR q.
  Proof. split; [done | apply _]. Qed.

  #[local] Definition SharedPtrHandleR_const_C :=
    [CANCEL] SharedPtrHandleR_const.
  #[local] Hint Opaque pieceHandle payload_releasable payload_allocation
    payload_destructible payload_deletable sptrInv : sl_opacity.

  Lemma SharedPtrR_const id pieceid Rpiece ownedPtr :
    const.CONST (shared_ptr_const_tu ty) (Tnamed (SP_name ty))
      (fun q => SharedPtrR q id pieceid Rpiece ownedPtr).
  Proof.
    const.prove.
    unfold SharedPtrR.
    go using SharedPtrHandleR_const_C.
  Qed.

  Lemma NullSharedPtrR_const :
    const.CONST (shared_ptr_const_tu ty) (Tnamed (SP_name ty))
      NullSharedPtrR.
  Proof. apply SharedPtrHandleR_const. Qed.

  Definition SharedPtrR_const_C := [CANCEL] SharedPtrR_const.
  Definition NullSharedPtrR_const_C := [CANCEL] NullSharedPtrR_const.


  Definition init_ctor :=
    specify {| info_name := (Nscoped ("std::shared_ptr".<<Atype ty>>) (Nctor [Tptr ty])).<<Atype ty, Atype "void">>
            ; info_type := tCtor ("std::shared_ptr".<<Atype ty>>) [Tptr ty] |} (fun (this:ptr) =>
    \arg{p:ptr} "ownedPtr" (Vptr p)
    (* Adoption may initialize enable_shared_from_this's internal weak handle.
       This interface frames the payload unchanged, so excludes that case. *)
    \pre [| shared_ptr_no_esftb ty = true |]
    \pre match ty with
         | Tarray _ _ => False
         | Tincomplete_array _ => False
         | _ => emp
        end
        
    \pre{Rpiece: nat -> Rep} [∗ list] pieceid ∈ allButFirstPieceId, p |-> Rpiece pieceid
    (* ^ morally, the caller gives up all the pieces and gets back the 0th piece. The remaining pieces get stored in the invariant.
       Should this object be destructed immediately, the destructor will need all the pieces to call delete. 
       We frame away the 0th piece in this spec. A derived spec can be proven where that framing away is not done *)
    \pre{tu op alignment} [| tu ⊧ σ |]
    \pre [| shared_ptr_delete_operator tu ty = Some op |]
    \pre p |-> alloc.tokenR_with_alignment ty alignment 1%Qp
    (* ^ gets stored in the invariant. only gets taken out when the count becomes 0, to call delete. at that time the ownership of all other pieces are also taken out from the invariant *)
    \pre payload_deletable ty op alignment Rpiece
    \post Exists (ctrlBlockId: CtrlBlockId),
       [| payload_type ctrlBlockId = ty |] **
       [| payload_delete ctrlBlockId = Some (op, alignment) |] **
       this |-> SharedPtrR 1$m ctrlBlockId 0 Rpiece p
         ** ([∗ list] pieceid ∈ allButFirstPieceId, pieceRight ctrlBlockId pieceid)
         (*  ^ the right to create [maxContention-1] more shared_ptr objects on this payload and claim the correponsing Rpiece ownerships at copy construction *)
      ).

  Definition SpecFor_init_ctor := RegisterSpec init_ctor.
  #[global] Existing Instance SpecFor_init_ctor.

  Notation spty := ("std::shared_ptr".<<Atype ty>>).
  Definition move_ctor :=
    specify.template.ctor spty [Trv_ref ((Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \pre{ctrlBlockId pieceid ownedPtr Rpiece} other |-> SharedPtrR 1$m ctrlBlockId pieceid Rpiece ownedPtr
    \post other  |-> NullSharedPtrR 1$m
          ** this |-> SharedPtrR 1$m ctrlBlockId pieceid Rpiece ownedPtr.

  Definition SpecFor_move_ctor := RegisterSpec move_ctor.
  #[global] Existing Instance SpecFor_move_ctor.

  Definition dtor_spec :=
    specify.template.dtor spty $
    \this this
    \pre{(null:bool) (p:ptr) (sid: if null then unit else prod CtrlBlockId nat) Rpiece}
      (* The handle lives at [this]; its outstanding payload piece lives at [p]. *)
      (match null as b return (if b then unit else prod CtrlBlockId nat) -> mpred with
                | false => fun sid=>
                             this |-> SharedPtrR 1$m sid.1 sid.2 Rpiece p
                             ** p |-> Rpiece sid.2
                | true => fun sid=> this |-> NullSharedPtrR 1$m
                end) sid

    \post (match null as b return (if b then unit else prod CtrlBlockId nat) -> mpred with
                | false => fun sid=> pieceRight sid.1 sid.2
                | true => fun sid=> emp
                end) sid.
  
  Definition SpecFor_dtor := RegisterSpec dtor_spec.
  #[global] Existing Instance SpecFor_dtor.


  Definition copy_ctor :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \prepost{q (null : bool) id source_pieceid p Rpiece}
      if null then other |-> NullSharedPtrR q
      else other |-> SharedPtrR q id source_pieceid Rpiece p
    \pre{pieceid}
      if null then emp
      else pieceRight id pieceid ** [| N.of_nat pieceid < Npos maxContention |]%N
    \post
      if null then this |-> NullSharedPtrR 1$m
      else p |-> Rpiece pieceid ** this |-> SharedPtrR 1$m id pieceid Rpiece p.

  Definition SpecFor_copy_ctor := RegisterSpec copy_ctor.
  #[global] Existing Instance SpecFor_copy_ctor.

  (** These are derived specializations, not independent registered library
      assumptions. Empty copying neither acquires a piece nor changes a count. *)
  Definition copy_ctor_nonnull :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \prepost{q id source_pieceid p Rpiece} other |-> SharedPtrR q id source_pieceid Rpiece p
    \pre{pieceid} pieceRight id pieceid (* this will be returned by destructor *)
    \pre [| N.of_nat pieceid < Npos maxContention|]%N
    \post
         p|->Rpiece pieceid ** this  |-> SharedPtrR 1$m id pieceid Rpiece p.
                          
  Definition copy_ctor_null :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \prepost{q} other |-> NullSharedPtrR q
    \post this  |-> NullSharedPtrR 1$m.

  #[local] Hint Opaque SharedPtrR NullSharedPtrR : sl_opacity.

  Lemma copy_ctor_nonnull_from_copy : copy_ctor |-- copy_ctor_nonnull.
  Proof.
    unfold copy_ctor, copy_ctor_nonnull.
    apply specify_mono_fupd. go.
    rewrite <- fupd_intro.
    iExists q, false, id, source_pieceid, p, Rpiece, pieceid.
    go.
    rewrite <- fupd_intro. go.
  Qed.

  Lemma copy_ctor_null_from_copy : copy_ctor |-- copy_ctor_null.
  Proof.
    unfold copy_ctor, copy_ctor_null.
    apply specify_mono_fupd. go.
    rewrite <- fupd_intro.
    iExists q, true,
      {| pieceRightLocs := []; pieceHandleLocs := [];
         dataLoc := nullptr; payload_type := ty; payload_delete := None |},
      0%nat, nullptr, (fun _ => emp), 0%nat.
    go.
    rewrite <- fupd_intro. go.
  Qed.

  (** Reconstruct the most-derived object pointer from the base-subobject "this". *)
  Definition upcast_offset (mid: Z) : offset :=
    (o_derived σ (SP_acc ty mid) (SP_impl ty) ,, o_derived σ (SP_impl ty) spty).

  Definition deref :=
    specify.template.op (SP_acc ty 0) OOStar function_qualifiers.Nc (Tref ty) [] $
       \this this
       \prepost{q id pieceid p Rpiece} this |-> (upcast_offset 0) |-> SharedPtrR q id pieceid Rpiece p
       \post[Vref p] emp.

  Definition SpecFor_deref := RegisterSpec deref.
  #[global] Existing Instance SpecFor_deref.
  #[global] Hint Opaque deref : sl_opacity.

  Definition arrow :=
    specify.template.op (SP_acc ty 0) OOArrow function_qualifiers.Nc (Tptr ty) [] $
       \this this
       \prepost{q id pieceid p Rpiece} this |-> (upcast_offset 0) |-> SharedPtrR q id pieceid Rpiece p
       \post[Vptr p] emp.

  Definition SpecFor_arrow := RegisterSpec arrow.
  #[global] Existing Instance SpecFor_arrow.
  #[global] Hint Opaque arrow : sl_opacity.
  
  #[global] Instance sharedR_typeptr_observe q id pieceid (p:ptr) op Rpiece
    : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype ty>>)) p) (p|->SharedPtrR q id pieceid Rpiece op):= _.
  
  Definition observeSharedTypeF q id pieceid t Rpiece op:= @observe_fwd _ _ _ (sharedR_typeptr_observe q id pieceid t Rpiece op).

  End tty.

  Definition init_ctor_arr ety :=
    specify {| info_name := (Nscoped ("std::shared_ptr".<<Atype (Tincomplete_array ety)>>) (Nctor [Tptr ety])).<<Atype ety, Atype "void">>
            ; info_type := tCtor ("std::shared_ptr".<<Atype (Tincomplete_array ety)>>) [Tptr ety] |} (fun (this:ptr) =>
    \arg{p:ptr} "ownedPtr" (Vptr p)
    \pre{Rpiece: nat -> Rep} [∗ list] pieceid ∈ allButFirstPieceId, p |-> Rpiece pieceid
    (* ^ morally, the caller gives up all the pieces and gets back the 0th piece. The remaining pieces get stored in the invariant.
       Should this object be destructed immediately, the destructor will need all the pieces to call delete. 
       We frame away the 0th piece in this spec. A derived spec can be proven where that framing away is not done *)
    \let{len} ty := Tarray ety len
    \pre{tu op alignment} [| tu ⊧ σ |]
    \pre [| shared_ptr_delete_operator tu ty = Some op |]
    \pre p |-> alloc.tokenR_with_alignment ty alignment 1%Qp
    (* ^ gets stored in the invariant. only gets taken out when the count becomes 0, to call delete. at that time the ownership of all other pieces are also taken out from the invariant *)
    \pre payload_deletable ty op alignment Rpiece
    \post Exists (ctrlBlockId: CtrlBlockId),
       [| payload_type ctrlBlockId = ty |] **
       [| payload_delete ctrlBlockId = Some (op, alignment) |] **
       this |-> SharedPtrR (Tincomplete_array ety) 1$m ctrlBlockId 0 Rpiece p
         ** ([∗ list] pieceid ∈ allButFirstPieceId, pieceRight ctrlBlockId pieceid)
         (*  ^ the right to create [maxContention-1] more shared_ptr objects on this payload and claim the correponsing Rpiece ownerships at copy construction *)
      ).
  
  Definition SpecFor_init_ctor_arr := RegisterSpec init_ctor_arr.
  #[global] Existing Instance SpecFor_init_ctor_arr.

  Definition subscript ety:=
    specify.template.op (SP_acc (Tincomplete_array ety) 1) OOSubscript function_qualifiers.Nc (Tref ety) ["long"%cpp_type] $
      \this this
      \arg{index} "index" (Vint index)
      \prepost{q id pieceid p Rpiece} this |-> (upcast_offset (Tincomplete_array ety) 1) |-> SharedPtrR (Tincomplete_array ety ) q id pieceid Rpiece p
      \pre{len : N} [| payload_type id = Tarray ety len |]
      \pre [| (0 <= index < Z.of_N len)%Z |]
      \post[Vref (p.[ety ! index])] emp.

  Definition SpecFor_subscript := RegisterSpec subscript.
  #[global] Existing Instance SpecFor_subscript.

  #[global] Hint Opaque
    init_ctor move_ctor dtor_spec copy_ctor copy_ctor_nonnull copy_ctor_null
    deref arrow init_ctor_arr subscript
    : sl_opacity.

End specs.
#[global] Hint Opaque SharedPtrR NullSharedPtrR payload_destructible
  payload_deletable payload_releasable payload_allocation : sl_opacity.
#[global] Hint Resolve SharedPtrR_const_C NullSharedPtrR_const_C : sl_opacity.
#[global]
  Hint Resolve observeSharedTypeF : sl_opacity.
Ltac sharedPtrRpieceFromPost :=
  match goal with
    H: context[@PostCondition ?a ?b ?c ?d] |- _
    => match c with
       | context[SharedPtrR _ _ _ _ ?rp _ ] => constr:(rp)
       end                            
  end.
