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

  Lemma update_b_ok : verify[source] "C::update_b(long)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.

    rewrite P.unlock /=.
    destruct args as [a [b []]]; simpl; go.
    iExists TT, _, _, (mk a (trim 64 (b + x))).
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

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    iExists TT.
    go.
    iExists TT.
    go.
    erewrite recursive_mutex.update_eq; last done; cbn.
    destruct args as [a[b []]]; simpl.
    work.
  Qed.

End with_cpp.

