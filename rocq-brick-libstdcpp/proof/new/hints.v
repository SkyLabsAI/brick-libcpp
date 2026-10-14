Require Import skylabs.auto.persistent.
Require Import skylabs.auto.cpp.hints.alignment.
Require Import skylabs.auto.cpp.hints.sizeof.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.new.spec.

#[only(lazy_unfold(global))] derive alloc.tokenR_with_alignment.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** ** Hints for proving [alloc.token] from [new_token.R].

     - <<_using_>> hints rely on [size_of _ ty = Some ...] to already be provable, while non
       <<using>> hints introduce this fact and have higher hint cost.
       This fact is otherwise lost because it is expressed within [alloc.token].
     - <<_0>> lemmas special case for non-array allocations which are common and ensure that
       the allocation overhead at the C++ level is 0. (Allocation overhead of the allocator-level is
       separately captured in [allocatedR].)
   *)
  #[program]
  Definition token_prove_using_C (p : ptr) (q : Qp) (alignment : option N)
      (storage_p : ptr) (overhead : N) (ty : type) (sz : N)
    (_ : size_of _ ty = Some sz) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \proving p |-> alloc.tokenR_with_alignment ty alignment q
    \through storage_p .[ Tbyte ! -overhead ] |-> allocatedR q (is_array_type ty) alignment (overhead + sz)
    \end.
  Next Obligation.
    rewrite alloc.tokenR_with_alignment.unlock. work.
  Qed.

  #[program]
  Definition token_prove_C (p : ptr) (q : Qp) (alignment : option N)
      (storage_p : ptr) (overhead : N) (ty : type) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \proving p |-> alloc.tokenR_with_alignment ty alignment q
    \deduce{sz} [| size_of _ ty = Some sz |]
    \through storage_p .[ Tbyte ! -overhead ] |-> allocatedR q (is_array_type ty) alignment (overhead + sz)
    \end.
  Next Obligation.
    intros; iIntros "X".
    iDestruct (observe [| exists sz, size_of _ _ = _ |] with "X") as "%"; first apply _.
    destruct H; simpl in *.
    rewrite alloc.tokenR_with_alignment.unlock. iDestruct "X" as "?"; work.
  Qed.

  (* special cases for the above two hints when the overhead is 0 *)
  #[program]
  Definition token_prove_using_0_C (p : ptr) (q : Qp) (alignment : option N)
      (storage_p : ptr) (ty : type) (sz : N)
    (_ : size_of _ ty = Some sz) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p 0)
    \proving p |-> alloc.tokenR_with_alignment ty alignment q
    \through storage_p |-> allocatedR q (is_array_type ty) alignment sz
    \end.
  Next Obligation.
    rewrite alloc.tokenR_with_alignment.unlock. work.
    normalize_ptrs. iStopProof; f_equiv. f_equiv. lia.
  Qed.

  #[program]
  Definition token_prove_0_C (p : ptr) (q : Qp) (alignment : option N)
      (storage_p : ptr) (ty : type) :=
    \cancelx
    \consuming p |-> new_token.R q (new_token.mk ty storage_p 0)
    \proving p |-> alloc.tokenR_with_alignment ty alignment q
    \deduce{sz} [| size_of _ ty = Some sz |]
    \through storage_p |-> allocatedR q (is_array_type ty) alignment sz
    \end.
  Next Obligation.
    intros; iIntros "X".
    iDestruct (observe [| exists sz, size_of _ _ = _ |] with "X") as "%"; first apply _.
    destruct H; simpl in *.
    rewrite alloc.tokenR_with_alignment.unlock. iDestruct "X" as "?"; work.
    normalize_ptrs. iStopProof; f_equiv; f_equiv; lia.
  Qed.


  (** ** Hints for proving [new_token.R] *)
  #[program]
  Definition token_use_non_array_C (p : ptr) (ty : type)
      (alignment : option N) (q : Qp) (_ : TCEq (is_array_type ty) false) :=
    \cancelx
    \consuming p |-> alloc.tokenR_with_alignment (σ:=σ) ty alignment q
    \proving{(storage_p : ptr) overhead} p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \deduce{(storage_p' : ptr) sz} [| size_of _ ty = Some sz |]
    \deduce storage_p' |-> allocatedR q false alignment sz
    \through [| storage_p = storage_p' |]
    \through [| overhead = 0 |]%N
    \end.
  Next Obligation.
    intros * Harray.
    rewrite alloc.tokenR_with_alignment.unlock (proj1 (TCEq_eq _ _) Harray).
    iIntros "X"; iDestruct "X" as (????) "[X ?]".
    iDestruct (observe [| overhead = 0%N |] with "X") as "%".
    subst. normalize_ptrs.
    iExists storage_p.
    iDestruct "X" as "?".
    work.
  Qed.

  (* Like [token_use_non_array_C], but with the size computed on [tu]:
     otherwise [size_of] of a class type stays symbolic and cannot meet the
     concrete size passed to a sized deallocation function. *)
  #[program]
  Definition token_use_non_array_tu_C tu (p : ptr) (ty : type)
      (alignment : option N) (q : Qp) n (_ : TCEq (is_array_type ty) false)
      (_ : _size_of tu ty =[Vm]=> Some n) :=
    \cancelx
    \preserving denoteModule tu
    \consuming p |-> alloc.tokenR_with_alignment (σ:=σ) ty alignment q
    \proving{(storage_p : ptr) overhead} p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \deduce{(storage_p' : ptr)} storage_p' |-> allocatedR q false alignment n
    \through [| storage_p = storage_p' |]
    \through [| overhead = 0 |]%N
    \end.
  Next Obligation.
    intros * Harray Hn%RedEq_eq.
    rewrite alloc.tokenR_with_alignment.unlock (proj1 (TCEq_eq _ _) Harray).
    iIntros "[#M X]"; iDestruct "X" as (storage_p overhead sz Hsz) "[X R]".
    iDestruct (observe [| _ ⊧ _ |] with "M") as %Hmod.
    have ? : sz = n by have := @sizeof._size_of_ok tu σ Hmod ty n Hn; congruence.
    iDestruct (observe [| overhead = 0%N |] with "X") as "%".
    subst. normalize_ptrs.
    iExists storage_p. iDestruct "R" as "?".
    work. iExact "X".
  Qed.

  #[program]
  Definition token_use_array_C (p : ptr) (ty : type)
      (alignment : option N) (q : Qp) :=
    \cancelx
    \consuming p |-> alloc.tokenR_with_alignment (σ:=σ) ty alignment q
    \proving{(storage_p : ptr) overhead} p |-> new_token.R q (new_token.mk ty storage_p overhead)
    \deduce{(storage_p' : ptr) (overhead' : N) sz} [| size_of _ ty = Some sz |]
    \deduce storage_p' .[ Tbyte ! -overhead' ] |-> allocatedR q (is_array_type ty) alignment (overhead' + sz)
    \through [| storage_p = storage_p' |]
    \through [| overhead = overhead' |]%N
    \end.
  Next Obligation.
    rewrite alloc.tokenR_with_alignment.unlock. work.
    iExists storage_p.
    work.
    iExists overhead. work.
  Qed.

  (** Resolve the alignment of a [tokenR] (see [alloc.default_new_alignment]). *)
  #[program]
  Definition token_default_alignment_C tu (p : ptr) ty q al
    (_ : _align_of tu ty =[Vm]=> Some al) :=
    \cancelx
    \preserving denoteModule tu
    \proving p |-> alloc.tokenR_with_alignment ty (alloc.default_new_alignment ty) q
    \through p |-> alloc.tokenR_with_alignment ty
      (if (STDCPP_DEFAULT_NEW_ALIGNMENT <? al)%N then Some al else None) q
    \end.
  Next Obligation.
    intros * Hal%RedEq_eq. iIntros "#M T".
    iDestruct (observe [| _ ⊧ _ |] with "M") as %?.
    by rewrite /alloc.default_new_alignment (_align_of_ok _ _ _ Hal).
  Qed.

  #[program]
  Definition token_default_alignment_F tu (p : ptr) ty q al
    (_ : _align_of tu ty =[Vm]=> Some al) :=
    \fwd
    \preserving denoteModule tu
    \using p |-> alloc.tokenR_with_alignment ty (alloc.default_new_alignment ty) q
    \deduce p |-> alloc.tokenR_with_alignment ty
      (if (STDCPP_DEFAULT_NEW_ALIGNMENT <? al)%N then Some al else None) q
    \end.
  Next Obligation.
    intros * Hal%RedEq_eq. iIntros "[#M T]".
    iDestruct (observe [| _ ⊧ _ |] with "M") as %?.
    iFrame "M". by rewrite /alloc.default_new_alignment (_align_of_ok _ _ _ Hal).
  Qed.

  #[global] Instance alloc_token_new_token_learnable ty alignment q q' a b c :
    Learnable (alloc.tokenR_with_alignment ty alignment q) (new_token.R q' (new_token.mk a b c)) [ty = a].
  Proof. solve_learnable. Qed.
  #[global] Instance token_learn : Cbn (Learn (learn_eq ==> learn_eq ==> learn_eq ==> any ==> learn_hints.fin) alloc.tokenR_with_alignment).
  Proof. solve_learnable. Qed.

  (** The alignment of a type declared in the translation unit is supported
      (<https://eel.is/c++draft/basic.align#4>); this covers the alignment
      argument that <<new T>> passes for an over-aligned <<T>>. *)
  #[program]
  Definition supported_alignment_tu_C `{!allocation_alignment_support σ} tu al
      (_ : existsb (fun nm => bool_decide (_align_of tu (Tnamed nm) = Some al))
             (map fst (map_to_list tu.(types))) =[Vm]=> true) :=
    \cancelx
    \preserving denoteModule tu
    \proving [| supported_alignment al |]
    \end.
  Next Obligation.
    intros * Hex%RedEq_eq. iIntros "#M".
    iDestruct (observe [| _ ⊧ _ |] with "M") as %Hmod.
    have Hsup : supported_alignment al.
    { apply existsb_exists in Hex as (nm & _ & Hal%bool_decide_eq_true_1).
      apply (supported_alignment_of_type (Tnamed nm)). by eapply _align_of_ok. }
    work.
  Qed.

End with_cpp.


#[global] Hint Resolve token_prove_C token_prove_0_C | 100 : sl_opacity.
#[global] Hint Resolve token_prove_using_C token_prove_using_0_C | 99 : sl_opacity.
#[global] Hint Resolve token_use_non_array_C | 99 : sl_opacity.
#[global] Hint Resolve token_use_non_array_tu_C | 98 : sl_opacity.
#[global] Hint Resolve token_use_array_C | 100 : sl_opacity.
#[global] Hint Resolve supported_alignment_tu_C : sl_opacity.
#[global] Hint Resolve token_default_alignment_C | 50 : sl_opacity.
#[global] Hint Resolve token_default_alignment_F : sl_opacity.
