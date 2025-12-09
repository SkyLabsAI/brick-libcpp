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
Definition P `{Σ : cpp_logic, σ : genv} (this : ptr) : TT -t> mpred :=
  fun (a b : Z) =>
    this ,, _field "C::balance_a" |-> intR 1$m a **
    this ,, _field "C::balance_b" |-> intR 1$m b.

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
  Context `{Σ : cpp_logic}.
  Context `{MOD : source ⊧ σ}. (* σ is the whole program *)
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context {has_rmutex : HasOwn mpredI recursive_mutex.cmraR}.

  cpp.spec "C::update_a(int)" as C_update_a with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) b) args) (P this)).

  cpp.spec "C::update_b(int)" as C_update_b with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{γ q} this |-> CR γ q
     \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
     \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
     \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk a (b + x)) args) (P this)).

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

  #[program]
  Definition own_P_is_acquireable_C' γ n :=
    \cancelx
    \preserving{th} current_thread th
    \consuming own γ.(level_gname) (◯E (S n, th))
    \bound (P : TT -t> mpred)
    \bound_existential th'
    \bound_existential st
    \proving acquireable (TT := TT) γ th' st P
    \instantiate th' := th
    \bound a b
    \instantiate st := Held n (mk a b)
    \through tele_app P (mk a b)
    \end.
  Next Obligation. rewrite acquireable.unlock; work. Qed.
  (* XXX this hint isn't robust because [a] and [b] become evars bound. *)


  Lemma update_a_ok : verify[source] "C::update_a(int)".
  Proof.
    verify_spec; go.
    iExists _, TT, (P this), _, th.
    go.

    rewrite P.unlock /=.
    destruct args as [a [b []]]; simpl; go.
    wfocus [| valid<_> _|] "". {
      admit. (* TODO make the addition modulo arithmetic in the spec *)
    }
    go.
    iExists _, TT, (P this).
    rewrite P.unlock.
    iExists _, th.
    iExists n, (mk (a + x) b).
    go.
    rewrite P.unlock. go.
    erewrite recursive_mutex.update_eq; last done.
    work.
    all: fail.
  Admitted.

  cpp.spec "C::transfer(int)" with
    (\this this
      \arg{x} "x" (Vint x)
      \prepost{γ q} this |-> CR γ q
      \prepost{q'} recursive_mutex.token γ.(recursive_mutex.lock_gname) q'
      \pre{args th} recursive_mutex.acquireable γ th args (TT:=TT) (P this)
      \post recursive_mutex.acquireable γ th (TT:=TT) (recursive_mutex.update (TT:=TT) (fun (a b : Z) => mk (a+x) (b-x)) args) (P this)).

  Lemma transfer_ok : verify[source] "C::transfer(int)".
  Proof.
    verify_spec; go.
    iExists γ, TT, (P this), _, th.
    go.
    iExists γ.
    rewrite !P.unlock /=.
    work.
    destruct args as [a[b []]]; simpl.
    work.

    Set Warnings "-br-hint-leading-to-dangling-evars".
    go using own_P_is_acquireable_C'.
    Set Warnings "br-hint-leading-to-dangling-evars".

    wfocus [| valid<_> _|] "". {
      admit. (* TODO make the addition modulo arithmetic in the spec *)
    }

    rewrite !P.unlock /=.
    go.
    iExists _, TT, (P this), _, th.
    rewrite !P.unlock /=.
    work.
    erewrite recursive_mutex.update_eq; last done.
    rewrite !P.unlock /=.
    work.
    all: fail.
  Admitted.

End with_cpp.

