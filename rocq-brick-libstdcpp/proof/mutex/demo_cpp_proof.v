Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.mutex.spec.
Require Import bluerock.brick.libstdcpp.mutex.demo_cpp.


(* TODO: generalizable *)
#[global] Instance own_learn {PROP : bi} {A : ofe} `{!HasOwn PROP (excl_authR A)} γ (a b : A) :
  Learnable (own γ (◯E a)) (own γ (◯E b)) [a = b].
Proof. solve_learnable. Qed.

Definition TT : tele := [tele (_ : Z) (_ : Z)].

Polymorphic Definition mk (a b : Z) : TT :=
  {| tele_arg_head := a; tele_arg_tail := {| tele_arg_head := b; tele_arg_tail := () |} |}.
Succeed Definition b := recursive_mutex.Held 0 (mk 0 0).

br.lock
Definition CR' `{Σ : cpp_logic, σ : genv} (a b : Z) : Rep :=
    _field "C::balance_a" |-> ulongR 1$m a **
    _field "C::balance_b" |-> ulongR 1$m b.
#[only(lazy_unfold)] derive CR'.
#[only(timeless)] derive CR'.

br.lock
Definition P `{Σ : cpp_logic, σ : genv} (this : ptr) : TT -t> mpred :=
  fun (a b : Z) => this |-> CR' a b.

br.lock
Definition CR
    `{Σ : cpp_logic, σ : genv, HasOwn mpredI recursive_mutex.cmraR}
    (γ : recursive_mutex.rmutex_gname) (q : cQp.t) : Rep :=
  structR "C" q **
  _field "C::mut" |-> recursive_mutex.R γ.(recursive_mutex.lock_gname) q **
  as_Rep (fun this : ptr =>
    recursive_mutex.inv_rmutex γ (∃ a_b : tele_arg _, tele_app (P this) a_b)).

#[only(cfractional,ascfractional,type_ptr)] derive CR.
#[only(lazy_unfold)] derive CR.

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

  #[program]
  Definition acquireable_acquireable_C γ :=
    \cancelx
    \consuming{th n args P} acquireable (TT := TT) γ th (Held n args) P
    \bound P'
    \bound_existential th' args'
    \proving acquireable γ th' args' P'
    \instantiate th' := th
    \instantiate args' := Held n args
    \deduce tele_app P args
    \through tele_app P' args
    \end.
  Next Obligation. rewrite acquireable.unlock; work. Qed.

  Hint Resolve acquireable_acquireable_C : br_hints.

  #[global] Instance : `{Learnable
    (current_thread th)
    (acquireable (TT := TT0) γ th0 args P0)
    [th0 = th] }.
  Proof. solve_learnable. Qed.

  #[global] Instance : `{Learnable
    (inv_rmutex γ1 P1)
    (inv_rmutex γ2 P2)
    [γ2 = γ1] }.
  Proof. solve_learnable. Qed.

  #[global] Instance : `{Learnable
    (inv_rmutex γ1 (∃ xs : tele_arg TT, tele_app P1 xs))
    (inv_rmutex γ2 (∃ xs : tele_arg TT, tele_app P2 xs))
    [P2 = P1] }.
  Proof. solve_learnable. Qed.


  Lemma update_a_ok : verify[source] "C::update_a(long)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.

    rewrite P.unlock /=.
    destruct args as [a [b []]]; simpl; go.
    iExists TT, _, _, (mk (trim 64 (a + x)) b).
    go.
    erewrite recursive_mutex.update_eq; last done; cbn.
    rewrite P.unlock; work.
  Qed.

  cpp.spec "C::transfer(int)" from demo_cpp.source with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (trim 64 (a+x)) (trim 64 (b-x))) args) (P this)).

  (* XXX this hint isn't robust because [a] and [b] become evars bound. *)
  (* #[program]
  Definition own_P_is_acquireable_C' γ n :=
    \cancelx
    \preserving{th} current_thread th
    \consuming own γ.(level_gname) (◯E (S n, th))
    \bound (P : TT -t> mpred)
    \bound_existential st
    \proving acquireable (TT := TT) γ th st P
    \bound a b
    \instantiate st := Held n (mk a b)
    \through tele_app P (mk a b)
    \end.
  Next Obligation. rewrite acquireable.unlock; work. Qed. *)

  #[program]
  Definition own_P_is_acquireable_C' γ n :=
    \cancelx
    \preserving{th} current_thread th
    \consuming own γ.(level_gname) (◯E (S n, th))
    \with (this : ptr)
    \consuming{a b} this |-> CR' a b
    \bound_existential st
    \proving acquireable (TT := TT) γ th st (λ a b, this |-> CR' a b)
    \instantiate st := Held n (mk a b)
    \end.
  Next Obligation. rewrite acquireable.unlock; work. Qed.
  #[local] Hint Resolve own_P_is_acquireable_C' : br_hints.

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.
    destruct args as [a[b []]]; rewrite !P.unlock /=.
    go.
    rewrite !P.unlock /=.
    go.
    iExists TT.
    work.
    erewrite recursive_mutex.update_eq; last done; cbn.
    rewrite !P.unlock /=.
    work.
  Qed.

End with_cpp.

