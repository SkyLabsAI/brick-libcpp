(** Client regressions for factory spec discovery, forwarding, const payloads,
    and retention of constructor side effects. These assume make_shared's
    library spec; they do not verify its reference-count implementation. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.shared_ptr.make_shared.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

#[elaborate]
cpp.prog source flags "-std=c++23" prog cpp:{{
#include <memory>
struct Payload {
    int value;
    explicit Payload(int n) : value(n) {}
};
std::shared_ptr<Payload> make_payload(int& n) {
    return std::make_shared<Payload>(n);
}
std::shared_ptr<Payload const> make_const_payload(int const& n) {
    return std::make_shared<Payload const>(n);
}
std::shared_ptr<Payload> make_rvalue_payload(int&& n) {
    return std::make_shared<Payload>(static_cast<int&&>(n));
}
std::shared_ptr<int const*> make_pointer_payload(int const*& p) {
    return std::make_shared<int const*>(p);
}
Payload* construct_payload(Payload* p, int& n) {
    return std::construct_at(p, n);
}
}}.

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : source ⊧ σ}.

  #[local] Instance learn_shared : LearnEq6 SharedPtrR :=
    ltac:(solve_learnable).

  Lemma payload_no_esft : shared_ptr_no_esftb "Payload" = true.
  Proof using MOD.
    eapply shared_ptr_no_esft_no_bases.
    { eapply (@glob_def_genv_compat_struct σ "Payload"%cpp_name source MOD).
      vm_compute. reflexivity. }
    { reflexivity. }
    { intros pack. split; discriminate. }
  Qed.

  cpp.spec "make_payload(int&)" from source as make_payload_spec with (
    \arg{argp : ptr} "n" (Vref argp)
    \prepost argp |-> type_ptrR "int"
    \pre{{D} (pieces : D -> nat -> Rep) before after}
      make_shared_construction "Payload" ["int&"%cpp_type] [Vref argp]
        pieces before after
    \pre before
    \post{retp : ptr} [Vptr retp]
      Exists (d : D) (id : CtrlBlockId) (p : ptr),
        [| payload_type id = "Payload"%cpp_type |] **
        retp |-> SharedPtrR "Payload" 1$m id 0 (pieces d) p **
        p |-> pieces d 0%nat **
        ([∗ list] i ∈ allButFirstPieceId, pieceRight id i) ** after d
  ).

  Lemma make_payload_ok : verify[source] make_payload_spec.
  Proof using MOD.
    have Hnoesft := payload_no_esft.
    verify_spec.
    go.
    iExists [Vref argp], D, pieces, before, after.
    go.
    match goal with d : D |- _ => iExists d end.
    go.
  Qed.

  cpp.spec "make_const_payload(const int&)" from source as make_const_payload_spec with (
    \arg{argp : ptr} "n" (Vref argp)
    \prepost argp |-> type_ptrR "int"
    \pre{{D} (pieces : D -> nat -> Rep) before after}
      make_shared_construction "Payload" ["const int&"%cpp_type] [Vref argp]
        pieces before after
    \pre before
    \post{retp : ptr} [Vptr retp]
      Exists (d : D) (id : CtrlBlockId) (p : ptr),
        [| payload_type id = "Payload"%cpp_type |] **
        retp |-> SharedPtrR "const Payload" 1$m id 0 (pieces d) p **
        p |-> pieces d 0%nat **
        ([∗ list] i ∈ allButFirstPieceId, pieceRight id i) ** after d
  ).

  Lemma make_const_payload_ok : verify[source] make_const_payload_spec.
  Proof using MOD.
    have Hnoesft := payload_no_esft.
    verify_spec.
    go.
    iExists [Vref argp], D, pieces, before, after.
    go.
    match goal with d : D |- _ => iExists d end.
    go.
  Qed.

  cpp.spec "make_rvalue_payload(int&&)" from source as make_rvalue_payload_spec with (
    \arg{argp : ptr} "n" (Vref argp)
    \prepost argp |-> type_ptrR "int"
    \pre{{D} (pieces : D -> nat -> Rep) before after}
      make_shared_construction "Payload" ["int"%cpp_type] [Vref argp]
        pieces before after
    \pre before
    \post{retp : ptr} [Vptr retp]
      Exists (d : D) (id : CtrlBlockId) (p : ptr),
        [| payload_type id = "Payload"%cpp_type |] **
        retp |-> SharedPtrR "Payload" 1$m id 0 (pieces d) p **
        p |-> pieces d 0%nat **
        ([∗ list] i ∈ allButFirstPieceId, pieceRight id i) ** after d
  ).

  Lemma make_rvalue_payload_ok : verify[source] make_rvalue_payload_spec.
  Proof using MOD.
    have Hnoesft := payload_no_esft.
    verify_spec.
    go.
    iExists [Vref argp], D, pieces, before, after.
    go.
    match goal with d : D |- _ => iExists d end.
    go.
  Qed.

  (* remove_cv_t removes only top-level qualifiers: the managed pointer's
     pointee must stay const, including in the construction obligation. *)
  cpp.spec "make_pointer_payload(const int*&)" from source as make_pointer_payload_spec with (
    \arg{argp : ptr} "p" (Vref argp)
    \prepost argp |-> type_ptrR "const int*"
    \pre{{D} (pieces : D -> nat -> Rep) before after}
      make_shared_construction "const int*" ["const int*&"%cpp_type] [Vref argp]
        pieces before after
    \pre before
    \post{retp : ptr} [Vptr retp]
      Exists (d : D) (id : CtrlBlockId) (p : ptr),
        [| payload_type id = "const int*"%cpp_type |] **
        retp |-> SharedPtrR "const int*" 1$m id 0 (pieces d) p **
        p |-> pieces d 0%nat **
        ([∗ list] i ∈ allButFirstPieceId, pieceRight id i) ** after d
  ).

  Lemma make_pointer_payload_ok : verify[source] make_pointer_payload_spec.
  Proof using MOD.
    verify_spec.
    go.
    iExists [Vref argp], D, pieces, before, after.
    go.
    match goal with d : D |- _ => iExists d end.
    go.
  Qed.

  Definition PayloadR (q : cQp.t) (n : Z) : Rep :=
    structR "Payload" q ** _field "Payload::value" |-> intR q n.
  #[local] Hint Opaque PayloadR : sl_opacity.

  cpp.spec "Payload::Payload(int)" from source as payload_ctor_spec with (
    fun (this : ptr) =>
      \arg{n : Z} "n" (Vint n)
      \post this |-> PayloadR 1$m n
  ).

  Lemma payload_ctor_ok : verify[source] payload_ctor_spec.
  Proof using MOD.
    verify_spec.
    go.
    rewrite /PayloadR.
    go.
  Qed.

  cpp.spec "Payload::~Payload()" from source as payload_dtor_spec with (
    fun (this : ptr) =>
      \pre{n} this |-> PayloadR 1$m n
      \post emp
  ).

  Lemma payload_dtor_ok : verify[source] payload_dtor_spec.
  Proof using MOD.
    verify_spec.
    rewrite /PayloadR.
    go.
  Qed.

  cpp.spec "operator new(unsigned long, void*)" from source
      as placement_new_spec with (
    \arg{size : N} "size" (Vn size)
    \arg{p : ptr} "p" (Vptr p)
    \post [Vptr p] emp
  ).

  Lemma placement_new_ok : verify[source] placement_new_spec.
  Proof using MOD.
    verify_spec.
    go.
  Qed.

  (* The client supplies a partition of genuine field ownership, not a
     constructor axiom for an arbitrary [Rpiece]. *)
  #[local] cpp.spec "std::forward<int&>(int&)" inline.
  Lemma construct_payload_ok {D : Type}
      (q : cQp.t) (qflag : Qp) (argp : ptr) (n : Z)
      (pieces : D -> nat -> Rep) (after : D -> mpred) :
    verify[source]
      (make_shared_construction "Payload" ["int&"%cpp_type] [Vref argp]
        pieces
        (argp |-> intR q n **
         _global "std::is_array_v<Payload>" |-> boolR qflag$c false **
         Forall p : ptr, p |-> PayloadR 1$m n -*
           Exists d : D, p |-> ([∗ list] i ∈ allPieceIds, pieces d i) **
             payload_destructible "Payload" (pieces d) ** after d)
        (fun d => argp |-> intR q n **
         _global "std::is_array_v<Payload>" |-> boolR qflag$c false ** after d)).
  Proof using MOD.
    verify_spec.
    go.
    change (size_of σ "Payload" = Some size) in a.
    rewrite (@sizeof._size_of_ok source σ MOD "Payload" 4 eq_refl) in a.
    injection a as Hsize. subst size.
    rewrite (@alignment._align_of_ok source σ MOD "Payload" 4 eq_refl) in b.
    injection b as Halign. subst alignment.
    go.
    rewrite (bi.forall_elim _x_4).
    wapply (bi.wand_elim_l (_x_4 |-> PayloadR 1$m n)
      (Exists d : D, _x_4 |-> ([∗ list] i ∈ allPieceIds, pieces d i) **
        payload_destructible "Payload" (pieces d) ** after d)).
    go.
  Qed.

  Lemma construct_payload_from_code {D : Type} (q : cQp.t) (qflag : Qp)
      (argp : ptr) (n : Z) (pieces : D -> nat -> Rep) (after : D -> mpred) :
    denoteModule source |--
      make_shared_construction "Payload" ["int&"%cpp_type] [Vref argp]
        pieces
        (argp |-> intR q n **
         _global "std::is_array_v<Payload>" |-> boolR qflag$c false **
         Forall p : ptr, p |-> PayloadR 1$m n -*
           Exists d : D, p |-> ([∗ list] i ∈ allPieceIds, pieces d i) **
             payload_destructible "Payload" (pieces d) ** after d)
        (fun d => argp |-> intR q n **
         _global "std::is_array_v<Payload>" |-> boolR qflag$c false ** after d).
  Proof using MOD.
    wapply (construct_payload_ok q qflag argp n pieces after).
    go using (spec_bwd payload_ctor_ok), (spec_bwd payload_dtor_ok),
      (spec_bwd placement_new_ok).
  Qed.
End with_cpp.
