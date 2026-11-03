(** libstdc++'s packed-bit specialization with its default allocator.
    This library boundary is independent of any application or bytecode model.
    These are assumed method specs; allocation failure is not excluded by
    their normal-return postconditions. Custom allocators are not covered. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.allocator.spec.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".

(** Instantiate the library declarations, including the proxy's special
    members, for cpp.spec. This function is only an AST fixture. *)
#[elaborate]
cpp.prog source prog cpp:{{
#include <vector>
void vector_bool_interface(std::vector<bool>& bits, unsigned long i, bool b) {
    std::vector<bool> fresh(1, b);
    bits[i] = b;
    bool x = bits[i];
    bool y = static_cast<std::vector<bool> const&>(bits)[i];
    std::vector<bool> moved(static_cast<std::vector<bool>&&>(fresh));
}
}}.

  (** Definition sketch: own the vector and _Bvector_base/_Bvector_impl
      subobjects, the allocator, the start/finish bit iterators and the
      end-of-storage pointer. Existentially own the allocated unsigned-long
      array beginning at [data], its capacity and allocation token. The
      finish iterator encodes [length bits]; bit i of that word array equals
      bits[i]. Padding bits are existential, not forced to zero. Empty and
      moved-from vectors may use nullptr without owning an array there.

      [q] fractions cover both the descriptor and the actual packed words.
      Full ownership is required to update a bit or destroy/move the vector.
      There is intentionally no lemma giving independent writable ownership
      of two bits: different bits may share one word. A proxy owns only its
      descriptor; reading/writing through it also requires this live storage
      with the matching [data] and an in-range index. *)
Parameter VectorBoolR : forall `{Sigma : cpp_logic} {CU : genv},
  cQp.t -> ptr -> list bool -> Rep.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  #[global] Instance VectorBoolR_type_ptr q data bits :
    Observe (type_ptrR "std::vector<bool, std::allocator<bool>>")
      (VectorBoolR q data bits).
  Admitted.
  Definition VectorBoolR_type_ptr_F :=
    ltac:(mk_at_obs_fwd VectorBoolR_type_ptr).
  #[global] Instance learn_VectorBoolR : LearnEq3 VectorBoolR :=
    ltac:(solve_learnable).

  (** The actual libstdc++ proxy fields. This owns no vector storage. The
      supported target has 64-bit unsigned long, matching _S_word_bit. *)
  Definition BitReferenceR (q : cQp.t) (data : ptr) (index : N) : Rep :=
    structR "std::_Bit_reference" q **
    _field "std::_Bit_reference::_M_p" |->
      primR (Tptr Tulong) q
        (Vptr (data .[Tulong ! Z.of_N (index / 64)])) **
    _field "std::_Bit_reference::_M_mask" |->
      ulongR q (2 ^ Z.of_N (index mod 64)).

  #[global] Instance BitReferenceR_type_ptr q data index :
    Observe (type_ptrR "std::_Bit_reference") (BitReferenceR q data index).
  Proof. unfold BitReferenceR. apply _. Qed.
  Definition BitReferenceR_type_ptr_F :=
    ltac:(mk_at_obs_fwd BitReferenceR_type_ptr).
  #[global] Instance learn_BitReferenceR : LearnEq3 BitReferenceR :=
    ltac:(solve_learnable).

  #[local] Hint Opaque VectorBoolR BitReferenceR : sl_opacity.

  cpp.spec "std::vector<bool, std::allocator<bool>>::vector(unsigned long, const bool&, const std::allocator<bool>&)"
    from source as vector_bool_fill_ctor_spec with (fun (this : ptr) =>
      \arg{size : N} "size" (Vn size)
      \arg{valuep : ptr} "value" (Vref valuep)
      \arg{allocp : ptr} "allocator" (Vref allocp)
      \prepost{qvalue b} valuep |-> boolR qvalue b
      \prepost{qalloc} allocp |-> std.allocator.R Tbool qalloc ()
      (* LP64 ptrdiff_t and rounded word-count bound: 2^63 - 64. *)
      \pre [| (size <= 9223372036854775744)%N |]
      \post Exists data,
        this |-> VectorBoolR 1$m data (replicateN size b)
    ).

  cpp.spec "std::vector<bool, std::allocator<bool>>::vector(std::vector<bool, std::allocator<bool>>&&)"
    from source as vector_bool_move_ctor_spec with (fun (this : ptr) =>
      \arg{other : ptr} "other" (Vref other)
      \pre{data bits} other |-> VectorBoolR 1$m data bits
      \post this |-> VectorBoolR 1$m data bits **
        other |-> VectorBoolR 1$m nullptr []
    ).

  cpp.spec "std::vector<bool, std::allocator<bool>>::~vector()"
    from source as vector_bool_dtor_spec with (fun (this : ptr) =>
      \pre{data bits} this |-> VectorBoolR 1$m data bits
      \post emp
    ).

  cpp.spec "std::vector<bool, std::allocator<bool>>::operator[](unsigned long)"
    from source as vector_bool_index_spec with (fun (this : ptr) =>
      \arg{index : N} "index" (Vn index)
      \prepost{q data bits} this |-> VectorBoolR q data bits
      \pre [| (index < N.of_nat (length bits))%N |]
      \post{retp : ptr} [Vptr retp] retp |-> BitReferenceR 1$m data index
    ).

  cpp.spec "std::vector<bool, std::allocator<bool>>::operator[](unsigned long) const"
    from source as vector_bool_index_const_spec with (fun (this : ptr) =>
      \arg{index : N} "index" (Vn index)
      \prepost{q data bits} this |-> VectorBoolR q data bits
      \pre [| (index < N.of_nat (length bits))%N |]
      \post[Vbool (nth (N.to_nat index) bits false)] emp
    ).

  cpp.spec "std::_Bit_reference::operator=(bool)"
    from source as bit_reference_assign_spec with (fun (this : ptr) =>
      \arg{b : bool} "value" (Vbool b)
      \prepost{data index} this |-> BitReferenceR 1$m data index
      \pre{(vectorp : ptr) bits} vectorp |-> VectorBoolR 1$m data bits
      \pre [| (index < N.of_nat (length bits))%N |]
      \post[Vref this]
        vectorp |-> VectorBoolR 1$m data (<[N.to_nat index := b]> bits)
    ).

  cpp.spec "std::_Bit_reference::operator bool() const"
    from source as bit_reference_read_spec with (fun (this : ptr) =>
      \prepost{qref data index} this |-> BitReferenceR qref data index
      \prepost{(vectorp : ptr) q bits} vectorp |-> VectorBoolR q data bits
      \pre [| (index < N.of_nat (length bits))%N |]
      \post[Vbool (nth (N.to_nat index) bits false)] emp
    ).

  cpp.spec "std::_Bit_reference::~_Bit_reference()"
    from source as bit_reference_dtor_spec with (fun (this : ptr) =>
      \pre{data index} this |-> BitReferenceR 1$m data index
      \post emp
    ).
End with_cpp.

#[global] Hint Opaque VectorBoolR BitReferenceR : sl_opacity.
#[global] Hint Resolve VectorBoolR_type_ptr_F BitReferenceR_type_ptr_F : sl_opacity.
