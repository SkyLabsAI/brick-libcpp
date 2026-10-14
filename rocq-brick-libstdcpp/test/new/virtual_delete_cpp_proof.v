Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.hints.alignment.
Require Import skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.new.spec_exc.
Require Import skylabs.brick.libstdcpp.new.hints.
Require skylabs.brick.libstdcpp.test.new.demo_cpp.
Import cfractional.cQp_compat.

(** * Over-aligned virtual delete

    <<delete p>> with <<p : PolyBase*>> pointing to an <<AlignedPoly>> deletes
    the most-derived object with the deallocation function that
    <<AlignedPoly>>'s virtual destructor selects
    (<https://eel.is/c++draft/expr.delete#8.1>,
    <https://eel.is/c++draft/class.dtor#15>): the aligned, sized global one,
    whose specification must be satisfied by the aligned allocation token. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} `{MOD : demo_cpp.source ⊧ σ}.
  Context `{alignment_support : !allocation_alignment_support σ}.

  Import linearity.

  Example aligned_poly_delete_for :
    delete_operator.delete_for demo_cpp.source false "operator delete(void*, unsigned long)" "AlignedPoly" =
      Some ("operator delete(void*, unsigned long, enum std::align_val_t)"%cpp_name,
            delete_operator.mk None true true).
  Proof. vm_compute. reflexivity. Qed.

  Abbreviation _derivedPA := (_derived "PolyBase" "AlignedPoly") (only parsing).
  Abbreviation _basePA := (_base "AlignedPoly" "PolyBase") (only parsing).

  Definition PolyBaseR (mdc : list globname) (q : Qp) : Rep :=
    structR "PolyBase" q ** derivationR "PolyBase" (mdc ++ ["PolyBase"])%cpp_name q.
  #[local] Hint Opaque PolyBaseR : sl_opacity typeclass_instances.
  #[only(type_ptr)] derive PolyBaseR.

  Definition AlignedPolyR (mdc : list globname) (q : Qp) : Rep :=
    let mdc' := (mdc ++ ["AlignedPoly"])%cpp_name in
    structR "AlignedPoly" q ** _basePA |-> PolyBaseR mdc' q **
    derivationR "AlignedPoly" mdc' q.
  #[local] Hint Opaque AlignedPolyR : sl_opacity typeclass_instances.
  #[only(type_ptr)] derive AlignedPolyR.

  cpp.spec "AlignedPoly::~AlignedPoly()" from demo_cpp.source as aligned_poly_dtor with
    (\this this
     \pre this |-> AlignedPolyR [] 1
     \post emp).

  (** Deleting through <<PolyBase>> an <<AlignedPoly>> that owns its aligned
      allocation token. *)
  Abbreviation aligned_poly_vdeleteI :=
    (vdeleteI "operator delete(void*, unsigned long)" "PolyBase" (TT := [tele])
      (_derivedPA |-> AlignedPolyR [] 1)
      (\this this
       \pre this ,, _derivedPA |->
              (AlignedPolyR [] 1 **
               alloc.tokenR_with_alignment "AlignedPoly" (Some 64%N) 1)
       \post emp)) (only parsing).

  cpp.spec "test_delete_aligned_poly(PolyBase*)" from demo_cpp.source as test_delete_aligned_poly_spec with
    (\arg{p} "p" (Vptr p)
     \pre p ,, _derivedPA |->
            (AlignedPolyR [] 1 **
             alloc.tokenR_with_alignment "AlignedPoly" (Some 64%N) 1)
     \post emp).

  Lemma test_delete_aligned_poly_ok :
    denoteModule demo_cpp.source ** aligned_poly_vdeleteI |-- test_delete_aligned_poly_spec.
  Proof using MOD. verify_spec; go. Qed.

  Lemma aligned_poly_vdeleteI_ok :
    denoteModule demo_cpp.source ** aligned_poly_dtor ** operator_delete_size_align
    |-- aligned_poly_vdeleteI.
  Proof using MOD alignment_support.
    #[local] Transparent vdeleteI_with.
    (* Anonymous: automation does not use named premises. *)
    iIntros "#(? & ? & ?)". rewrite /vdeleteI_with.
    iModIntro.
    iExists ["AlignedPoly"%cpp_name].
    setoid_rewrite <-(bi.exist_intro demo_cpp.source).
    iExists _, _, _, _. work.
    2: normalize_ptrs; go; normalize_ptrs; go.
    rewrite /AlignedPolyR /PolyBaseR. normalize_ptrs. work.
  Qed.
End with_cpp.
