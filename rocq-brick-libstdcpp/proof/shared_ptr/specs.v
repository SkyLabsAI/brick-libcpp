(** Specs of shared_ptr.
We do not cover interaction with weak_ptr.
We cover the following usage:
- after dynamically allocating a new object (using new or new[]), it is (typicall immediately) passed to the init constructor of shared_ptr (spec in [init_ctor] below). At this time, the caller's proof needs to come up with [Rpiece: nat->Rep], defining how the ownership of this newly allocated object will be split between various shared_ptr objects that refer to it. They pass in all pieces and get back the 0th piece: [Rpiece 0] and tokens [pieceRight ctrlid 1 ... pieceRight ctrlid (maxContention-1)] which the clients can use to later obtain ownership of those [Rpiece]s by calling the copy constructor. The last argument of [pieceRight] is the piece id. The first argument, [ctrlid], identifies a single protection unit (payload object pointer) that is reference counted. "ctrl" comes from the implementation using a dynamically allocated "control block" which has an atomic counter to track how many times the copy constructor has been called minus the number of such objects that have already been destructed.
[maxContention] bounds the number of simultaneously live handles to one control
block. For the supported libstdc++ ABI it is [INT_MAX], not the pointer-sized
unsigned maximum; see the definition below.

The init constructor requires [payload_destructible]: collecting every payload
piece must suffice to run the managed object's destruction. This persistent
capability becomes part of [SharedPtrR]. Unlike a plain entailment to [anyR],
it allows ghost updates before destruction and accounts for nontrivial member
destructors. It must be supplied by the constructor's caller, not assumed as
an unconditional property of arbitrary payload predicates.

The pieces may not always be fractional ownerships of an object (e.g. int). For example, when the shared_ptr protects an array, it is common to have every piece own an index of the array, so that different shared_ptr objects can be used to write to different indices concurrently, e.g. here: https://github.com/category-labs/monad/blob/90f8b796061aeaf78a2943c45eae5303f6ff7900/category/execution/ethereum/execute_block.cpp#L233

- To gain confidence in the provability of these specs, we sketch a definition of [SharedPtrR]. The [inv] definition is the most tricky part of it: it stores all the [Rpiece] and [pieceRight] ownerships that need to be dished out later or to be used for deletion when the reference count goes to 0.
Because BRiCk only supports SC atomics, the proof only works as if the stdlib implementation used SC atomics or had sufficient barriers (the actual defn of SharedPtrR will be different in that case due to limitations on invariants in weak memory reasoning).

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

- These specs in this file allow you to change the ownership split protocol (between the various shared_ptr objects protecting the same payload object ptr) later on (see lemma [redistributePayloadOwnership]), as long as the caller can cough up all pieces and objects associated with the payload (see [allPiecesAndObjs]).
A common pattern where this can be useful is when the thread that calls new needs to initialize the object after wrapping it in a shared_ptr but before sharing it with other concurrent threads. So until that event, it will have the exclusive ownership of the entire object (Rpiece n = emp for n>0, Rpiece 0= objR 1) and later, we redistribute with (Rpiece n => objR (1/N)).

*)

Require Import skylabs.auto.cpp.proof.
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
Require Import iris.algebra.excl.
Require Import iris.algebra.frac.

NES.Open std.atomic.


Record CtrlBlockId : Set :=
  {
    pieceRightLocs: list gname; (* each stores a unit. N -> gname may be tricky for constructor proof *)
    pieceHandleLocs: list gname; (* Fractional outstanding-index witnesses. *)
    dataLoc: ptr;
    payload_type: type; (* Complete allocation type, including the length of an array. *)
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

Definition ctrOffset: offset. Proof. Admitted.
(** offset of the field storing ownedPtr in any shared_ptr object *)
Definition ownedPtrOffset: offset. Proof. Admitted. 
(** offset of the field storing ctrlBlock pointer in any shared_ptr object *)
Definition ctrlBlockPtrOffset: offset. Proof. Admitted. 

Definition maxContentionQp := pos_to_Qp maxContention.
Definition allPieceIds : list nat := (seq 0 (Pos.to_nat maxContention)).
Definition allButFirstPieceId := (seq 1 (Pos.to_nat maxContention -1 )).

Definition countLN {A : Type} (f : A -> bool) (l : list A) : N :=
  lengthN (filter f l).

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


  Section tty. Context (ty:type).

  Import linearity.


  (* just an exclusive token for each pieceid. can be defined with a simpler CMRA as fractionality is not needed. fgptsoQ has good automation support  *)
  Definition pieceRight ctrlid pieceid : mpred :=
    match nth_error (pieceRightLocs ctrlid) pieceid with
    | Some g => own (A := exclR unitO) g (Excl ())
    | None => emp (* bad argument, pieceid > maxContention *)
    end.

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
    (dataLoc id),, ctrOffset |-> atomic.R "long" 1 (Z.of_N ctrVal)
         ** ([∗ list] pieceid ∈ allPieceIds,
               if pieceOut pieceid then pieceRight id pieceid
               else pieceHandle id 1 pieceid)
         ** (if (bool_decide (ctrVal = 0))
              then emp
              else ownedPtr |-> alloc.tokenR (payload_type id) 1%Qp
                    ** ([∗ list] pieceid ∈ allPieceIds,
                      if pieceOut pieceid then emp else ownedPtr |-> Rpiece pieceid)).
  
  (** Currently, we assume the control block is just an atomic counter.
      In reality, it is probably a struct. so move the atomicR to some defn ctrlBlockR *)
  (* [q] describes this handle, not the shared control block or a payload
     piece. In particular, splitting [q] does not create a [pieceRight]. *)
  Definition SharedPtrR (q : cQp.t) (id: CtrlBlockId) (pieceid : nat)
      (Rpiece : nat -> Rep) (ownedPtr:ptr) : Rep :=
    structR ("std::shared_ptr".<<Atype ty>>) q
    ** [| delete_compat ty (payload_type id) |]
    ** pureR (payload_destructible (payload_type id) Rpiece)
    ** ownedPtrOffset |-> primR (Tptr ty) q (Vptr ownedPtr)
    ** ctrlBlockPtrOffset |-> primR (Tptr (Tnamed ("std::atomic".<<Atype "long">>))) q (Vptr (dataLoc id))
    ** [| ownedPtr<>nullptr |] (* use NullSharedPtr otherwise *)
    ** [| lengthN (pieceRightLocs id) = Npos maxContention |]
    ** [| lengthN (pieceHandleLocs id) = Npos maxContention |]
    ** [| (N.of_nat pieceid < Npos maxContention)%N |]
    ** pureR (pieceHandle id (cQp.frac q) pieceid)
    ** pureR (inv nroot (Exists (pieceOut : nat ->bool), sptrInv id Rpiece ownedPtr pieceOut)).

  Definition NullSharedPtrR (q : cQp.t) : Rep :=
    structR ("std::shared_ptr".<<Atype ty>>) q
    ** ownedPtrOffset |-> primR (Tptr ty) q (Vptr nullptr)
    ** ctrlBlockPtrOffset |->  primR (Tptr (Tnamed ("std::atomic".<<Atype "long">>))) q (Vptr nullptr).

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


  Definition init_ctor :=
    specify {| info_name := (Nscoped ("std::shared_ptr".<<Atype ty>>) (Nctor [Tptr ty])).<<Atype ty, Atype "void">>
            ; info_type := tCtor ("std::shared_ptr".<<Atype ty>>) [Tptr ty] |} (fun (this:ptr) =>
    \arg{p:ptr} "ownedPtr" (Vptr p)
    \pre match ty with
         | Tarray _ _ => False
         | Tincomplete_array _ => False
         | _ => emp
        end
        
    \pre{Rpiece: nat -> Rep} [∗ list] pieceid ∈ allButFirstPieceId, p |-> Rpiece pieceid
    (* ^ morally, the caller gives up all the pieces and gets back the 0th piece. The remaining pieces get stored in the invariant.
       Should this object be destructed immediately, the destructor will need all the pieces to call delete. 
       We frame away the 0th piece in this spec. A derived spec can be proven where that framing away is not done *)
    \pre p |-> alloc.tokenR ty 1%Qp
    (* ^ gets stored in the invariant. only gets taken out when the count becomes 0, to call delete. at that time the ownership of all other pieces are also taken out from the invariant *)
    \pre payload_destructible ty Rpiece
    \post Exists (ctrlBlockId: CtrlBlockId),
       [| payload_type ctrlBlockId = ty |] **
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
    \prepost{q id source_pieceid p Rpiece} other |-> SharedPtrR q id source_pieceid Rpiece p
    \pre{pieceid} pieceRight id pieceid (* this will be returned by destructor *)
    \pre [| N.of_nat pieceid < Npos maxContention|]%N
    \post
         p|->Rpiece pieceid ** this  |-> SharedPtrR 1$m id pieceid Rpiece p.
                          
  Definition SpecFor_copy_ctor := RegisterSpec copy_ctor.
  #[global] Existing Instance SpecFor_copy_ctor.

  (** Copy-ctor from null: produces another null shared_ptr.
      No token is required. TODO: unify this spec with the spec above, using dependent types, as done in the destructor spec *)
  Definition copy_ctor_null :=
    specify.template.ctor spty [Tref (Tconst (Tnamed spty))] $
    \this this
    \arg{other:ptr} "other" (Vptr other)
    \prepost{q} other |-> NullSharedPtrR q
    \post this  |-> NullSharedPtrR 1$m.
               

  Definition SP_acc (mid: Z) := ("std::__shared_ptr_access" .<< 
                           Atype ty,
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy"),
                           Avalue (Eint mid "bool"),
                           Avalue (Eint 0 "bool") >>)%cpp_name.

  Definition SP_impl := ("std::__shared_ptr" .<< 
                           Atype ty,
                           Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

  (** Reconstruct the most-derived object pointer from the base-subobject "this". *)
  Definition upcast_offset (mid: Z) : offset :=
    (o_derived σ (SP_acc mid) SP_impl ,, o_derived σ SP_impl spty).

  Definition deref :=
    specify.template.op (SP_acc 0) OOStar function_qualifiers.Nc (Tref ty) [] $
       \this this
       \prepost{q id pieceid p Rpiece} this |-> (upcast_offset 0) |-> SharedPtrR q id pieceid Rpiece p
       \post[Vref p] emp.

  Definition SpecFor_deref := RegisterSpec deref.
  #[global] Existing Instance SpecFor_deref.
  #[global] Hint Opaque deref : sl_opacity.

  Definition arrow :=
    specify.template.op (SP_acc 0) OOArrow function_qualifiers.Nc (Tptr ty) [] $
       \this this
       \prepost{q id pieceid p Rpiece} this |-> (upcast_offset 0) |-> SharedPtrR q id pieceid Rpiece p
       \post[Vptr p] emp.

  Definition SpecFor_arrow := RegisterSpec arrow.
  #[global] Existing Instance SpecFor_arrow.
  #[global] Hint Opaque arrow : sl_opacity.
  
  #[global] Instance sharedR_typeptr_observe q id pieceid (p:ptr) op Rpiece
    : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype ty>>)) p) (p|->SharedPtrR q id pieceid Rpiece op):= _.
  
  Definition observeSharedTypeF q id pieceid t Rpiece op:= @observe_fwd _ _ _ (sharedR_typeptr_observe q id pieceid t Rpiece op).

  Definition allPiecesAndObjs Rpiece id (ownedPtr: ptr) (pieceOut: nat->bool) : Rep :=
   ([∗ list] pieceid ∈ allPieceIds,
     if pieceOut pieceid
     then pureR (ownedPtr |-> Rpiece pieceid)
          ** pureR (Exists (base:ptr), base |->SharedPtrR 1$m id pieceid Rpiece ownedPtr)
     else pureR (pieceRight id pieceid)).

  Lemma redistributePayloadOwnership {Rpieceold Rpiecenew: nat -> Rep} (pieceOut : nat -> bool) id ownedPtr:
    allPiecesAndObjs Rpieceold id ownedPtr pieceOut
      |-- |={⊤}=> allPiecesAndObjs Rpiecenew id ownedPtr pieceOut.
  Proof. Admitted.

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
    \pre p |-> alloc.tokenR ty 1%Qp
    (* ^ gets stored in the invariant. only gets taken out when the count becomes 0, to call delete. at that time the ownership of all other pieces are also taken out from the invariant *)
    \pre payload_destructible ty Rpiece
    \post Exists (ctrlBlockId: CtrlBlockId),
       [| payload_type ctrlBlockId = ty |] **
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
      \post[Vref (p.[ety ! index])] emp.

  Definition SpecFor_subscript := RegisterSpec subscript.
  #[global] Existing Instance SpecFor_subscript.

  #[global] Hint Opaque
    init_ctor move_ctor dtor_spec copy_ctor copy_ctor_null
    deref arrow init_ctor_arr subscript
    : sl_opacity.

End specs.
#[global]
  Hint Resolve observeSharedTypeF : sl_opacity.
Ltac sharedPtrRpieceFromPost :=
  match goal with
    H: context[@PostCondition ?a ?b ?c ?d] |- _
    => match c with
       | context[SharedPtrR _ _ _ _ ?rp _ ] => constr:(rp)
       end                            
  end.
