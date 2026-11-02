(** Allocation ownership for the default libstdc++ shared-pointer constructors.
    [SharedAllocationR] owns allocation tokens only. [ControlBlockRestR]
    separately owns the implicit weak count and the remaining control-block
    layout; neither owns payload fields or the strong-reference counter.

    Custom deleters, custom allocators, aliasing constructors, and
    make_shared_for_overwrite are not supported. The internal __sp_array_delete
    used by shared_ptr<T[]>(new T[n]) is the library's default array deleter,
    not support for a caller-supplied deleter.

    These definitions do not prove make_shared or add an assumed factory spec.
    They remove the requirement that a make_shared payload have its own
    allocator token. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.shared_ptr.layout.

Set Default Goal Selector "!".
Import linearity.

Inductive shared_allocation_kind : Set :=
| SeparateAllocation
| CombinedAllocation.

(** Array factories allocate using the innermost element type. *)
Fixpoint shared_array_element (ty : type) : type :=
  match ty with
  | Tarray ety _ => shared_array_element ety
  | Tqualified cv ety => Tqualified cv (shared_array_element ety)
  | _ => ty
  end.

Definition shared_control_name (kind : shared_allocation_kind)
    (payload_ty : type) : name :=
  match kind, erase_qualifiers payload_ty with
  | SeparateAllocation, Tarray _ _ =>
      ("std::_Sp_counted_deleter".<< Atype (Tptr (SP_element payload_ty)),
        Atype "std::__sp_array_delete", Atype "std::allocator<void>",
        Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name
  | SeparateAllocation, _ =>
      ("std::_Sp_counted_ptr".<< Atype (Tptr payload_ty),
        Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name
  | CombinedAllocation, Tarray _ _ =>
      ("std::_Sp_counted_array".<<
        Atype (Tnamed ("std::allocator".<<
          Atype (shared_array_element payload_ty) >>)),
        Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name
  | CombinedAllocation, _ =>
      ("std::_Sp_counted_ptr_inplace".<< Atype payload_ty,
        Atype "std::allocator<void>",
        Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name
  end.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (** Abstract physical ownership for the supported default-deleter control
      block, not a ghost capability or an invariant assertion. The dynamic
      class is [shared_control_name kind payload_ty]; [control] points to its
      _Sp_counted_base subobject and [owned] is its managed object.

      Own the dynamic-class/base identities, dispatch information, remaining
      initialized fields and padding. For separate allocation this includes
      the stored managed pointer; for in-place objects, the allocator/storage
      bookkeeping; for combined arrays, the element count, allocator and
      tail-layout bookkeeping consistent with [payload_ty] and [owned].

      Exclude BOTH reference-counter cells, payload ownership, allocation
      tokens and [provides_storage]: those are separate conjuncts. This token
      contains no outstanding-handle ghost names, so repartitioning the
      payload can preserve it unchanged. No creation, copying or disposal law
      is assumed here. The still-assumed library constructors must establish
      it from the control block they construct, and final release consumes it.

      TOFIXLATER: define this layout ownership for each supported libstdc++
      control-block class when proving the library bodies. This abstraction
      does not justify virtual dispatch, combined counter loads or weak-memory
      synchronization by itself. See shared-pointer PR #10:
      https://github.com/SkyLabsAI/brick-libcpp/pull/10 *)
  Parameter ControlBlockLayoutR :
    genv -> shared_allocation_kind -> type -> ptr -> ptr -> mpred.

  (** Part of the abstract field-ownership interface, not a proved layout law.
      Timelessness permits the existing ghost-only redistribution proof; it
      does not permit dropping ownership or removing later from arbitrary P. *)
  #[global] Declare Instance ControlBlockLayoutR_timeless kind ty control owned :
    Timeless (ControlBlockLayoutR CU kind ty control owned).

  (** With no external weak_ptr or enable_shared_from_this, every live strong
      ownership group retains exactly one implicit weak reference. The final
      release takes this ownership out of the invariant before changing the
      weak count or disposing of the control block. *)
  Definition ControlBlockRestR (kind : shared_allocation_kind)
      (payload_ty : type) (control owned : ptr) : mpred :=
    control ., (SP_counted_base .:: Nid "_M_weak_count") |-> intR 1$m 1 **
    ControlBlockLayoutR CU kind payload_ty control owned.

  #[global] Instance ControlBlockRestR_timeless kind ty control owned :
    Timeless (ControlBlockRestR kind ty control owned).
  Proof. unfold ControlBlockRestR. apply _. Qed.

  (** The storage used by _Sp_counted_ptr_inplace::_M_ptr(). Do not equate
      the placement-constructed object pointer to this storage pointer:
      [provides_storage] below records their relationship. *)
  Definition shared_inplace_storage (payload_ty : type) (root : ptr) : ptr :=
    let cn := shared_control_name CombinedAllocation payload_ty in
    root .,(cn .:: Nid "_M_impl")
         .,((cn .:: Nid "_Impl") .:: Nid "_M_storage")
         .,(("__gnu_cxx::__aligned_buffer".<< Atype payload_ty >>)
              .:: Nid "_M_storage").

  Definition SharedAllocationR (kind : shared_allocation_kind)
      (payload_ty : type) (payload_alignment : option N)
      (control owned : ptr) : mpred :=
    let cn := shared_control_name kind payload_ty in
    Exists root : ptr,
      [| control = root ,, o_base CU cn SP_counted_base |] **
      match kind with
      | SeparateAllocation =>
          Exists control_alignment,
            root |-> alloc.tokenR_with_alignment (Tnamed cn) control_alignment 1%Qp **
            owned |-> alloc.tokenR_with_alignment payload_ty payload_alignment 1%Qp
      | CombinedAllocation =>
          match erase_qualifiers payload_ty with
          | Tarray _ _ =>
              (* _Sp_counted_array is placement-constructed in the tail of
                 the element allocation. [offset] includes alignment padding;
                 [total] includes both objects and any unused tail bytes.
                 Retain the allocation at [storage], not at the tail object.
                 std::allocator uses scalar operator new, even for an array.
                 Keep its actual alignment argument for matching deallocation.
                 Exact _S_tail arithmetic and the other control-block fields
                 belong to a future verification of the library bodies. *)
              Exists (storage : ptr) (offset total payload_size control_size : N)
                  (alignment : option N),
                [| size_of CU payload_ty = Some payload_size |] **
                [| size_of CU (Tnamed cn) = Some control_size |] **
                [| (payload_size <= offset /\ offset + control_size <= total)%N |] **
                storage |-> allocatedR 1%Qp false alignment total **
                root |-> new_token.R 1%Qp
                  (new_token.mk (Tnamed cn) (storage .[ Tuchar ! Z.of_N offset ]) 0) **
                provides_storage storage owned payload_ty
          | _ =>
              (* One allocation for the enclosing control block, and only a
                 placement/storage relationship for the managed object. *)
              Exists alignment,
                root |-> alloc.tokenR_with_alignment (Tnamed cn) alignment 1%Qp **
                provides_storage (shared_inplace_storage payload_ty root)
                  owned payload_ty
          end
      end.
End with_cpp.

#[global] Hint Opaque SharedAllocationR ControlBlockRestR
  ControlBlockLayoutR : sl_opacity.
