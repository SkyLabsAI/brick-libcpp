Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.mutex.demo_cpp.


(* TODO: generalizable *)
#[global] Instance own_learn {PROP : bi} {A : ofe} `{!HasOwn PROP (excl_authR A)} γ (a b : A) :
  Learnable (own γ (◯E a)) (own γ (◯E b)) [a = b].
Proof. solve_learnable. Qed.

(** Data protected by our recursive mutex *)
sl.lock
Definition CR' `{Σ : cpp_logic, σ : genv} (a b : Z) : Rep :=
    _field "C::balance_a" |-> ulongR 1$m a **
    _field "C::balance_b" |-> ulongR 1$m b.
#[only(lazy_unfold)] derive CR'.
#[only(timeless)] derive CR'.

(** The telescope to pass CR' to [inv_rmutex]. Isomorphic to [Z * Z]. *)
Definition TT : tele := [tele (_ : Z) (_ : Z)].

(** Canonical "constructor" for our telescope. *)
Polymorphic Definition mk (a b : Z) : TT :=
  {| tele_arg_head := a; tele_arg_tail := {| tele_arg_head := b; tele_arg_tail := () |} |}.
Succeed Definition b := recursive_mutex.Held 0 (mk 0 0).

(** Proof that [mk] is injective. Doesn't appear to be necessary here. *)
#[global] Instance mk_inj: Inj2 eq eq eq mk.
Proof. rewrite /Inj2; naive_solver. Qed.

sl.lock
Definition P `{Σ : cpp_logic, σ : genv} (this : ptr) : TT -t> mpred :=
  fun (a b : Z) => this |-> CR' a b.

sl.lock
Definition CR
    `{Σ : cpp_logic, σ : genv, HasOwn mpredI recursive_mutex.cmraR}
    (γ : recursive_mutex.rmutex_gname) (q : cQp.t) : Rep :=
  structR "C" q **
  _field "C::mut" |-> recursive_mutex.R γ.(recursive_mutex.lock_gname) q **
  as_Rep (fun this : ptr =>
    recursive_mutex.inv_rmutex γ (∃ a_b : tele_arg _, tele_app (P this) a_b)).

#[only(cfractional,ascfractional,type_ptr)] derive CR.
#[only(lazy_unfold)] derive CR.

Section recursive_mutex.
  Import recursive_mutex.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context {has_rmutex : HasOwn mpredI recursive_mutex.cmraR}.

  Lemma acquireable_update_equiv {TT : tele} γ th f t1 t2 P :
    acquire t1 t2 ->
    acquireable γ th (update f t1) P ⊣⊢ acquireable γ th (release (TT := TT) (update f t2)) P.
  Proof.
    intros.
    by erewrite recursive_mutex.update_eq.
  Qed.
End recursive_mutex.

#[only(fwd(l2r))] derive acquireable_update_equiv.
#[only(bwd(l2r))] derive acquireable_update_equiv.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context {has_rmutex : HasOwn mpredI recursive_mutex.cmraR}.

  #[global] Instance: LearnEq2 CR'.
  Proof. solve_learnable. Qed.

  cpp.spec "C::update_a(long)" as C_update_a from demo_cpp.source with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (trim 64 (a+x)) b) args) (P this)).

  cpp.spec "C::update_b(long)" as C_update_b from demo_cpp.source with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk a (trim 64 (b + x))) args) (P this)).

  #[global] Instance CR_learn : Cbn (Learn (learn_eq ==> any ==> learn_hints.fin) CR).
  Proof. solve_learnable. Qed.

  Import recursive_mutex.

  #[global] Instance: `{Proper (equiv ==> equiv) (inv_rmutex γ)}.
  Proof. rewrite inv_rmutex.unlock. solve_proper. Qed.

  #[program]
  Definition inv_rmutex_iff_C γ :=
    \cancelx
    \preserving{P1} inv_rmutex γ P1
    \proving{P2} inv_rmutex γ P2
    \through [| P1 ⊣⊢@{mpredI} P2 |]
    \end.
  Next Obligation. work. by setoid_subst. Qed.
  (* #[local] Hint Resolve inv_rmutex_iff_C : br_hints. *)

  #[program]
  Definition inv_rmutex_wand_C γ :=
    \cancelx
    \preserving{P1} inv_rmutex γ P1
    \proving{P2} inv_rmutex γ P2
    \through □ (P1 ∗-∗ P2)
    \end.
  Next Obligation.
    rewrite inv_rmutex.unlock.
    iIntros "%% A %P2 #[? ?]".
    iApply (inv_iff with "A").
    iIntros "!> !>"; iSplit; ework with br_erefl; case_match; work.
  Qed.
  (* #[local] Hint Resolve inv_rmutex_wand_C : br_hints. *)

  Lemma CR'_tele_equiv (this : ptr) :
    (∃ a b : Z, this |-> CR' a b) ⊣⊢
    ∃ xs : TT, tele_app (TT := TT) (λ a b : Z, this |-> CR' a b) xs.
  Proof.
    iSplit.
    { iDestruct 1 as (a b) "?"; iExists (mk a b); work. }
    iDestruct 1 as ([a [b []]]) "?"; iExists a, b; work.
  Qed.
  #[local] Hint Resolve CR'_tele_equiv : br_hints.

  Lemma CR'_self_eq (this : ptr) :
    (∃ a b : Z, this |-> CR' a b) ⊣⊢
    (∃ a b : Z, this |-> CR' a b).
  Proof. done. Qed.
  #[local] Hint Resolve CR'_self_eq : br_hints.

  Lemma refl_equiv (P : mpred) : P ⊣⊢ P.
  Proof. done. Qed.
  #[local] Hint Resolve refl_equiv : br_hints.

  Lemma CR'_P_tele_equiv (this : ptr) :
    (∃ a_b : TT, tele_app (TT := TT) (λ a b, this |-> CR' a b) a_b) ⊣⊢
    (∃ a_b : TT, tele_app (P this) a_b).
  Proof. by rewrite P.unlock. Qed.
  #[local] Hint Resolve CR'_P_tele_equiv : br_hints.

  Lemma update_a_ok : verify[source] "C::update_a(long)".
  Proof.
    verify_spec; go.

  #[program]
  Definition inv_rmutex_iff_C γ :=
    \cancelx
    \preserving{P1} inv_rmutex γ P1
    \proving{P2} inv_rmutex γ P2
    \through [| P1 ⊣⊢@{mpredI} P2 |]
    \end.
  Next Obligation. work. by setoid_subst. Qed.
  #[local] Hint Resolve inv_rmutex_iff_C : br_hints.

    iExists TT.
    go.
    rewrite P.unlock.
    destruct args as [a [b []]]; simpl; go.
    iExists TT, (P this), _, (mk (trim 64 (a + x)) b).
    go.
    rewrite P.unlock.
    go.
    rewrite P.unlock.
    go.
    all: fail.
  Fail Qed.
  Admitted.

  Lemma update_b_ok : verify[source] "C::update_b(long)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.

    rewrite P.unlock.
    destruct args as [a [b []]]; simpl; go.
    iExists TT, _, _, (mk a (trim 64 (b + x))).
    go.
    rewrite P.unlock.
    go.
    rewrite P.unlock.
    go.
    all: fail.
  Fail Qed.
  Admitted.

  cpp.spec "C::transfer(int)" as C_transfer_int from demo_cpp.source with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (fun a b => this |-> CR' a b)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (trim 64 (a+x)) (trim 64 (b-x))) args) (fun a b => this |-> CR' a b)).

  Lemma P_CR'_tele_equiv (this : ptr) :
    (∃ a_b : TT, tele_app (P this) a_b) ⊣⊢
    (∃ a_b : TT, tele_app (TT := TT) (λ a b, this |-> CR' a b) a_b).
  Proof. by rewrite P.unlock. Qed.
  #[local] Hint Resolve P_CR'_tele_equiv : br_hints.

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.
    iExists (Held _ args).
    destruct args as [a [b []]]; simpl.
    go.
    rewrite P.unlock.
    go.
    rewrite P.unlock.
    go.
    iExists TT.
    go.
    all: fail.
  Fail Qed.
  Admitted.

  Lemma partial_transfer_link :
    denoteModule source ∗
      recursive_mutex.lock_spec' ∗ recursive_mutex.unlock_spec'
      ⊢ C_transfer_int.
  Proof.
    work.
    wapply transfer_ok.
    wapply update_a_ok.
    wapply update_b_ok.
    work.
  Qed.

End with_cpp.

