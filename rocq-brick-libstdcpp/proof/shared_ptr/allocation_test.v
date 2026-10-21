(** Regression checks for the allocation part of SharedPtrR. These are
    representation lemmas, not proofs of C++ factories or destructors. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.shared_ptr.layout.
Require Import skylabs.brick.libstdcpp.shared_ptr.allocation.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".
Import linearity.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (** The ordinary new/new[] route retains both allocation tokens. *)
  Example separate_allocations (ty : type) (root owned : ptr)
      (control_alignment payload_alignment : option N) :
    root |-> alloc.tokenR_with_alignment
      (Tnamed (shared_control_name SeparateAllocation ty)) control_alignment 1 **
    owned |-> alloc.tokenR_with_alignment ty payload_alignment 1
    |-- SharedAllocationR SeparateAllocation ty
          (root ,, o_base CU (shared_control_name SeparateAllocation ty)
            SP_counted_base) owned.
  Proof.
    unfold SharedAllocationR.
    rewrite <- (bi.exist_intro root).
    rewrite <- (bi.exist_intro control_alignment),
      <- (bi.exist_intro payload_alignment).
    go.
  Qed.

  (** A combined named object needs no token allocating the payload itself. *)
  Example combined_object (nm : name) (root owned : ptr)
      (alignment : option N) :
    root |-> alloc.tokenR_with_alignment
      (Tnamed (shared_control_name CombinedAllocation (Tnamed nm))) alignment 1 **
    provides_storage (shared_inplace_storage (Tnamed nm) root) owned (Tnamed nm)
    |-- SharedAllocationR CombinedAllocation (Tnamed nm)
          (root ,, o_base CU
            (shared_control_name CombinedAllocation (Tnamed nm)) SP_counted_base)
          owned.
  Proof.
    unfold SharedAllocationR.
    rewrite <- (bi.exist_intro root).
    cbn [erase_qualifiers].
    rewrite <- (bi.exist_intro alignment).
    go.
  Qed.

  (** The array allocation is owned at its beginning, not at the control block
      placed after the last element. The count remains in [Tarray ety len]. *)
  Example combined_array (ety : type) (len : N) (storage root owned : ptr)
      (offset total payload_size control_size : N)
      (alignment : option N)
      (cn := shared_control_name CombinedAllocation (Tarray ety len)) :
    size_of CU (Tarray ety len) = Some payload_size ->
    size_of CU (Tnamed cn) = Some control_size ->
    (payload_size <= offset /\ offset + control_size <= total)%N ->
    storage |-> allocatedR 1 false alignment total **
    root |-> new_token.R 1
      (new_token.mk (Tnamed cn) (storage .[ Tuchar ! Z.of_N offset ]) 0) **
    provides_storage storage owned (Tarray ety len)
    |-- SharedAllocationR CombinedAllocation (Tarray ety len)
          (root ,, o_base CU cn SP_counted_base) owned.
  Proof.
    intros Hpayload Hcontrol Hbounds.
    unfold SharedAllocationR.
    rewrite <- (bi.exist_intro root).
    cbn [erase_qualifiers].
    rewrite <- (bi.exist_intro storage), <- (bi.exist_intro offset),
      <- (bi.exist_intro total), <- (bi.exist_intro payload_size),
      <- (bi.exist_intro control_size), <- (bi.exist_intro alignment).
    go.
  Qed.
End with_cpp.

(** Template arguments must preserve const, unlike erased heap types. *)
Example const_array_control_name :
  shared_control_name SeparateAllocation "const int[2]" =
    ("std::_Sp_counted_deleter".<< Atype "const int*",
      Atype "std::__sp_array_delete", Atype "std::allocator<void>",
      Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.
Proof. reflexivity. Qed.

Example const_array_factory_control_name :
  shared_control_name CombinedAllocation "const int[2]" =
    ("std::_Sp_counted_array".<< Atype "std::allocator<const int>",
      Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.
Proof. reflexivity. Qed.
