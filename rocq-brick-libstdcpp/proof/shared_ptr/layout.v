(** The LP64 libstdc++ handle layout for the atomic lock policy. The pointee and
    control block are not subobjects of the handle. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.const.

Set Default Goal Selector "!".
Import linearity.

Definition SP_name (ty : type) : name :=
  ("std::shared_ptr".<< Atype ty >>)%cpp_name.

Definition SP_impl (ty : type) : name :=
  ("std::__shared_ptr".<< Atype ty,
    Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

Definition SP_acc (ty : type) (is_array : Z) : name :=
  ("std::__shared_ptr_access".<< Atype ty,
    Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy"),
    Avalue (Eint is_array "bool"),
    Avalue (Eint (if bool_decide (erase_qualifiers ty = Tvoid) then 1 else 0)
      "bool") >>)%cpp_name.

Definition SP_access (ty : type) : name :=
  SP_acc ty (if is_array_type (erase_qualifiers ty) then 1 else 0).

Definition SP_count : name :=
  ("std::__shared_count".<<
    Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

Definition SP_counted_base : name :=
  ("std::_Sp_counted_base".<<
    Avalue (Eint 2 "enum __gnu_cxx::_Lock_policy") >>)%cpp_name.

(** [shared_ptr<T[]>] stores [T*], not a pointer to an array. Keep cv qualifiers when
    removing exactly one array extent. *)
Fixpoint SP_element (ty : type) : type :=
  match ty with
  | Tarray ety _ | Tincomplete_array ety | Tvariable_array ety _ => ety
  | Tqualified cv ty => Tqualified cv (SP_element ty)
  | _ => ty
  end.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Definition SharedPtrHandleR (ty : type) (q : cQp.t)
      (owned control : ptr) : Rep :=
    structR (SP_name ty) q **
    _base (SP_name ty) (SP_impl ty) |->
      (structR (SP_impl ty) q **
       _base (SP_impl ty) (SP_access ty) |-> structR (SP_access ty) q **
       _field (SP_impl ty .:: Nid "_M_ptr") |->
         primR (Tptr (erase_qualifiers (SP_element ty))) q (Vptr owned) **
       _field (SP_impl ty .:: Nid "_M_refcount") |->
         (structR SP_count q **
          _field (SP_count .:: Nid "_M_pi") |->
            primR (Tptr (Tnamed SP_counted_base)) q (Vptr control))).

  #[global] Instance SharedPtrHandleR_fractional ty owned control :
    CFractional (fun q => SharedPtrHandleR ty q owned control) := _.

  #[global] Instance SharedPtrHandleR_typeptr ty q owned control :
    Observe (type_ptrR (Tnamed (SP_name ty)))
      (SharedPtrHandleR ty q owned control) := _.
End with_cpp.

#[global] Hint Opaque SharedPtrHandleR : sl_opacity.

(** A small type table makes LP64 ABI agreement an explicit, decidable obligation
    of clients. No declaration about the managed object is needed. *)
Definition SP_count_struct : Struct :=
  Build_Struct []
    [mkMember (field_name.Id "_M_pi") (Tptr (Tnamed SP_counted_base))
      false None (Build_LayoutInfo 0)]
    [] [] (SP_count .:: Ndtor) false None Standard 8 8.

Definition SP_access_struct (ty : type) : Struct :=
  Build_Struct [] [] [] []
    (SP_access ty .:: Ndtor) true None POD 1 1.

Definition SP_impl_struct (ty : type) : Struct :=
  Build_Struct [(SP_access ty, Build_LayoutInfo 0)]
    [mkMember (field_name.Id "_M_ptr") (Tptr (SP_element ty))
       false None (Build_LayoutInfo 0);
     mkMember (field_name.Id "_M_refcount") (Tnamed SP_count)
       false None (Build_LayoutInfo 64)]
    [] [] (SP_impl ty .:: Ndtor) false None Standard 16 8.

Definition SP_outer_struct (ty : type) : Struct :=
  Build_Struct [(SP_impl ty, Build_LayoutInfo 0)] [] [] []
    (SP_name ty .:: Ndtor) false None Standard 16 8.

Definition shared_ptr_const_tu (ty : type) : translation_unit :=
  makeTranslationUnit empty
    (NM.add (SP_name ty) (Gstruct (SP_outer_struct ty))
      (NM.add (SP_impl ty) (Gstruct (SP_impl_struct ty))
        (NM.add (SP_access ty) (Gstruct (SP_access_struct ty))
          (NM.add SP_count (Gstruct SP_count_struct) empty))))
    empty [] [] abi.abi_default empty empty empty empty.

#[local] Lemma SP_lookup_outer ty :
  (shared_ptr_const_tu ty).(types) !! SP_name ty =[Vm?]=>
    Some (Gstruct (SP_outer_struct ty)).
Proof.
  rewrite VmEq_eq_iff.
  change (NM.find (SP_name ty) (types (shared_ptr_const_tu ty)) =
    Some (Gstruct (SP_outer_struct ty))).
  apply complete_type.NMFacts.add_eq_o.
  apply NM.E.eq_refl.
Qed.

#[local] Lemma SP_lookup_impl ty :
  (shared_ptr_const_tu ty).(types) !! SP_impl ty =[Vm?]=>
    Some (Gstruct (SP_impl_struct ty)).
Proof.
  rewrite VmEq_eq_iff.
  change (NM.find (SP_impl ty) (types (shared_ptr_const_tu ty)) =
    Some (Gstruct (SP_impl_struct ty))).
  rewrite complete_type.NMFacts.add_neq_o.
  { apply complete_type.NMFacts.add_eq_o, NM.E.eq_refl. }
  { intro H. apply NM.eqL in H. discriminate. }
Qed.

#[local] Lemma SP_lookup_access ty :
  (shared_ptr_const_tu ty).(types) !! SP_access ty =[Vm?]=>
    Some (Gstruct (SP_access_struct ty)).
Proof.
  rewrite VmEq_eq_iff.
  change (NM.find (SP_access ty) (types (shared_ptr_const_tu ty)) =
    Some (Gstruct (SP_access_struct ty))).
  unfold shared_ptr_const_tu. cbn [types].
  rewrite -> complete_type.NMFacts.add_neq_o,
    complete_type.NMFacts.add_neq_o.
  { apply complete_type.NMFacts.add_eq_o, NM.E.eq_refl. }
  { intro H. apply NM.eqL in H. discriminate. }
  { intro H. apply NM.eqL in H. discriminate. }
Qed.

#[local] Lemma SP_lookup_count ty :
  (shared_ptr_const_tu ty).(types) !! SP_count =[Vm?]=>
    Some (Gstruct SP_count_struct).
Proof.
  rewrite VmEq_eq_iff.
  change (NM.find SP_count (types (shared_ptr_const_tu ty)) =
    Some (Gstruct SP_count_struct)).
  unfold shared_ptr_const_tu. cbn [types].
  rewrite -> complete_type.NMFacts.add_neq_o,
    complete_type.NMFacts.add_neq_o, complete_type.NMFacts.add_neq_o.
  { apply complete_type.NMFacts.add_eq_o, NM.E.eq_refl. }
  { intro H. apply NM.eqL in H. discriminate. }
  { intro H. apply NM.eqL in H. discriminate. }
  { intro H. apply NM.eqL in H. discriminate. }
Qed.

#[local] Hint Resolve SP_lookup_outer SP_lookup_impl SP_lookup_access
  SP_lookup_count | 0 : typeclass_instances sl_opacity.

Section const.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Lemma SharedPtrHandleR_const ty owned control :
    const.CONST (shared_ptr_const_tu ty) (Tnamed (SP_name ty))
      (fun q => SharedPtrHandleR ty q owned control).
  Proof.
    const.prove.
    unfold SharedPtrHandleR.
    go.
  Qed.
End const.
