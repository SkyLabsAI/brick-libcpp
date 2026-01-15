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

  Lemma tele_app_mk_beta (P : Z -> Z -> mpred) (x y : Z) :
    tele_app (TT := TT) (λ a b : Z, P a b) (mk x y) = P x y.
  Proof. reflexivity. Qed.

  (** "Eta-expand" [∃ xy : TT, ... tele_app P xy ... ] to [∃ (x y : Z), ... tele_app P (mk x y) ...].
  This is useful because [tele_app (λ a b : Z, Q a b) (mk x y)] simplifies to [Q x y] ([tele_app_mk_beta]). *)
  #[program] Definition learn_args_C (P : TT -t> mpred) :=
    \cancelx
    \bound_existential args
    \proving tele_app P args
    \exist a b
    \instantiate args := mk a b
    \through tele_app P (mk a b)
    \end.
  Next Obligation. work. Qed.
  #[local] Hint Resolve learn_args_C : br_hints.

  #[program] Definition P_unfold_split_args_F this args :=
    \cancelx
    \consuming tele_app (P this) args
    \intro a
    \intro b
    \deduce tele_app (TT := TT) (fun a b => this |-> CR' a b) (mk a b)
    \deduce [| args = mk a b |]
    \end.
  Next Obligation. iIntros (this [a [b []]]) "/= ?". iExists a, b. rewrite P.unlock. work. Qed.

  #[program] Definition P_unfold_B :=
    \cancelx
    \bound this a b
    \proving P this a b
    \through this |-> CR' a b
    \end.
  Next Obligation. rewrite P.unlock. work. Qed.

  Section unfold_P.
    #[local] Hint Resolve P_unfold_split_args_F : br_hints.
    #[local] Hint Resolve P_unfold_B : br_hints.

    Lemma update_a_ok : verify[source] "C::update_a(long)".
    Proof.
      verify_spec; go.
    Qed.

    Lemma update_b_ok : verify[source] "C::update_b(long)".
    Proof.
      verify_spec; go.
    Qed.
  End unfold_P.

  cpp.spec "C::transfer(int)" as C_transfer_int from demo_cpp.source with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (trim 64 (a+x)) (trim 64 (b-x))) args) (P this)).

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    destruct args as [a [b []]]; work.
  Qed.

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

