Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.auto.cpp.hints.invoke.
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
    #[local] Transparent vdeleteI.
    iIntros "#(M & Dt & D)". rewrite /vdeleteI.
    iModIntro.
    iExists ["AlignedPoly"%cpp_name].
    setoid_rewrite <-(bi.exist_intro demo_cpp.source).
    iExists _, _, _, _, _, _. work.
    - rewrite /AlignedPolyR /PolyBaseR. normalize_ptrs. work. by iFrame "M".
    - (* TODO: in this lemma (as in [consistency.v]), [go] selects none of
         [wp_delete_obj_C], [wp_destroy_val_named_C], [wp_invoke_delete_C] or
         [wp_invoke_O_unmaterialized_C], although their premises are solvable;
         they are applied explicitly. *)
      normalize_ptrs. iIntros.
      iDestruct select (_ |-> alloc.tokenR_with_alignment _ _ _)%I as "T".
      rewrite alloc.tokenR_with_alignment.unlock.
      iDestruct "T" as (storage overhead sz Hsz) "[T A]".
      match goal with |- environments.envs_entails _ (wp_delete_obj _ _ _ ?p ?K) =>
        iApply (new_delete.wp_delete_obj_C_obligation_1 demo_cpp.source false
          "operator delete(void*, unsigned long)" "AlignedPoly"
          ("operator delete(void*, unsigned long, enum std::align_val_t)"%cpp_name,
           delete_operator.mk None true true) p K ltac:(vm_compute; constructor) with "M") end.
      go. iFrame "T".
      eassert (find_spec.FindSpec σ false (_global "AlignedPoly::~AlignedPoly()") aligned_poly_dtor _)
        as HF by (typeclasses eauto).
      match goal with |- environments.envs_entails _ (wp_destroy_named _ _ ?this ?Q) =>
        iApply (invoke.wp_destroy_val_named_C_obligation_1 demo_cpp.source this "AlignedPoly"
          "AlignedPoly::~AlignedPoly()" _ aligned_poly_dtor Q _ ltac:(typeclasses eauto) MOD
          ltac:(typeclasses eauto) HF with "Dt") end.
      go.
      match goal with |- environments.envs_entails _ (wp_invoke_delete _ _ ?n ?p ?Q) =>
        iApply (new_delete.wp_invoke_delete_C_obligation_1 demo_cpp.source "AlignedPoly"
          "operator delete(void*, unsigned long, enum std::align_val_t)" true true n p Q
          ltac:(typeclasses eauto) with "M") end.
      go.
      match goal with |- environments.envs_entails _ (wp_invoke_O _ ?ft (inl (Vptr ?f)) ?args None ?Q) =>
        epose proof (wp_invoke_O_unmaterialized demo_cpp.source f _ _ _ _ _
          operator_delete_size_align _ ft args None _ ltac:(apply _)) as L end.
      specialize (L ltac:(reflexivity) ltac:(apply _) ltac:(apply _)).
      iDestruct (L with "D") as "[_ H]". iApply "H". go.
      iEval (rewrite _at_pureR) in "A". case_bool_decide; go.
      + (* [storage] holds a 64-byte block, so it is not null. *)
        iDestruct select (_ |-> blockR _ _)%I as "B".
        have ? : sz = 64%N.
        { have := sizeof._size_of_ok demo_cpp.source (Tnamed "AlignedPoly") 64 ltac:(by vm_compute).
          rewrite Hsz. congruence. }
        subst sz.
        iDestruct (observe (storage .[ "unsigned char" ! - overhead ] |-> nonnullR) with "B") as "N".
        { apply _at_observe, blockR_nonnull, TCLt_N; lia. }
        iExFalso. rewrite _at_nonnullR. iDestruct "N" as %Hnn. congruence.
      + iFrame "A". iIntros (r) "R". rewrite operand_receive.unlock /exact_operand_resultR.
        iExists Vvoid. iFrame.
  Qed.
End with_cpp.
