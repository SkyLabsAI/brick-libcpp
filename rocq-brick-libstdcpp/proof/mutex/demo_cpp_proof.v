Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.mutex.spec.
Require Import bluerock.brick.libstdcpp.mutex.demo_cpp.


(* TODO: generalizable *)
#[global] Instance own_learn {PROP : bi} {A : ofe} `{!HasOwn PROP (excl_authR A)} γ (a b : A) :
  Learnable (own γ (◯E a)) (own γ (◯E b)) [a = b].
Proof. solve_learnable. Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}. (* σ is the whole program *)
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context {has_rmutex : HasOwn mpredI recursive_mutex.cmraR}.

  Definition TT : tele := [tele (_ : Z) (_ : Z)].
  Definition mk (a b : Z) : TT :=
    {| tele_arg_head := a; tele_arg_tail := {| tele_arg_head := b; tele_arg_tail := () |} |}.

  Definition P (this : ptr) : TT -t> mpred :=
    fun (a b : Z) =>
       this ,, _field "C::balance_a" |-> intR 1$m a **
       this ,, _field "C::balance_b" |-> intR 1$m b.

  Definition CR (γ : gname) (q : cQp.t) : Rep :=
    structR "C" q **
    _field "C::mut" |-> recursive_mutex.R γ q **
    as_Rep (fun this : ptr =>
      recursive_mutex.inv_rmutex γ (∃ a_b : tele_arg _, tele_app (P this) a_b)).

  cpp.spec "C::update_a(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) b) args) (P this)).

  cpp.spec "C::update_b(int)" with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk a (b + x)) args) (P this)).

  Lemma update_a_ok : verify[source] "C::update_a(int)".
  Proof.
    verify_spec; go.
    rewrite /CR.
    iExists TT; iExists (P this); iExists q; iExists th.
    go.
    rewrite /P/=.
    (* Instance token_learn γ : LearnEq1 (recursive_mutex.token γ) := ltac:(solve_learnable). *)
    destruct args as [a [b []]]; simpl; go.
    iSplitR. { admit. (* TODO make the addition modulo arithmetic in the spec *) }
    Instance given_token_learn γ : LearnEq1 (recursive_mutex.given_token γ) :=
      ltac:(solve_learnable).
    go.
    iExists TT; iExists (P this).
    iExists th.
    iExists n, (mk (a + x) b).
    rewrite /P; go.
    (* Clients shouldn't unfold abstractions like [recursive_mutex.acquireable] *)
    rewrite /recursive_mutex.acquireable.
    work.
    erewrite recursive_mutex.update_eq; last done.
    go.
    rewrite /P; go.
    (* Clients shouldn't do case distinctions! *)
    destruct n; rewrite /recursive_mutex.acquireable; go.
    all: fail.
  Admitted.

  cpp.spec "C::transfer(int)" with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \prepost{q'} recursive_mutex.token γ q'
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) (b-x)) args) (P this)).

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    rewrite /CR. go.
    iExists TT; iExists (P this). iExists th. iExists _. go.
    iExists _; iExists th. go.
    iExists _; iExists th. go.
    cut_pure (valid<"int"> _).
    { admit. (* TODO make the addition modulo arithmetic in the spec *) }
    go.
    iExists TT; iExists (P this); iExists th; iExists _.
    work.
    iFrame.
    rewrite /CR. work.
    destruct n; subst; simpl; work.
    destruct args as [a[b?]]; simpl.
    have->: (b + (0 - x) = b - x)%Z by lia. done.
    all: fail.
  Admitted.

End with_cpp.

Import auto_frac auto_pick_frac.
