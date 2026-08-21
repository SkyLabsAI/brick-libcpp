Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.guard_recursive_cpp.

Import linearity.

Implicit Type (p : ptr) (σ : genv).

Definition TT : tele := [tele (_ : Z)].

#[global] Instance: Inhabited TT.
Proof. solve_inhabited. Qed.

(** Canonical "constructor" for our telescope. *)
Polymorphic Definition mk (a : Z) : TT :=
  {| tele_arg_head := a; tele_arg_tail := () |}.
Succeed Definition b := recursive_mutex.Held 0 (mk 0).

sl.lock
Definition CR' `{Σ : cpp_logic, σ : genv} (a : Z) : Rep :=
  _field "C::value" |-> intR 1$m a.
#[only(lazy_unfold(export))] derive CR'.
#[only(timeless)] derive CR'.

(** No *)
(* A := B *)
(** Yes *)
(* A := off |-> B. *)

(* p
p |->  *)

sl.lock
Definition P `{Σ : cpp_logic, σ : genv} (this : ptr) : TT -t> mpred :=
  fun (a : Z) => this |-> CR' a.

sl.lock
Definition CR
  `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}
  `{!recursive_mutex.lockedG Σ}
  `{!HasOwn (iPropI _) recursive_mutex.cmraR}
  (γ : recursive_mutex.rmutex_gname) (q : cQp.t) :=
  structR "C" q **
  _field "C::m" |-> recursive_mutex.R γ.(recursive_mutex.lock_gname) q **
  as_Rep (fun this : ptr =>
    recursive_mutex.inv_rmutex γ (∃ a : tele_arg TT, tele_app (P this) a)).

#[only(cfractional,ascfractional,cfracvalid,type_ptr)] derive CR.
#[only(lazy_unfold(export))] derive CR.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  Context `{!recursive_mutex.lockedG Σ}.
  Context `{!HasOwn (iPropI _) recursive_mutex.cmraR}.

  #[local] Instance: `{WeaklyObjective1 (tele_app (P p))}.
  Proof. Admitted.

  #[global] Instance P_timeless p a : Timeless (P p a).
  Proof. rewrite P.unlock; apply _. Qed.

  #[global] Instance P_timeless' p a : Timeless (tele_app (P p) a).
  Proof. destruct a. apply _. Qed.

  (* int value{0};
  std::recursive_mutex m; *)

  cpp.spec "test_one_answer()" from source with (
    \post[Vint 42] emp
  ).
  cpp.spec "test_other_answer()" from source with (
    \post[Vint 42] emp
  ).

  Import recursive_mutex(lock_gname).

  cpp.spec "C::C()" from source as C_ctor_spec with (
    \this this
    \persist{thr} current_thread thr
    \post Exists γ,
      this |-> CR γ 1$m **
      recursive_mutex.token (lock_gname γ) 1 **
      recursive_mutex.used_threads (lock_gname γ) {[thr]} **
      recursive_mutex.locked (lock_gname γ) thr 0
  ).

  #[global] Instance unfold (p' : ptr) : `{AutoUnlocking.DefinedUsing (P p n) (p' |-> CR' n')} := {}.

  Lemma C_ctor_ok :
    verify[source] "C::C()".
  Proof.
    verify_shift; go.
    iExists TT, (P this), (mk 0); go.
    rewrite {1}P.unlock.
    (* Ugh *)
    rewrite -bi.later_intro.
    go.

    iMod (recursive_mutex.use_thread thr (lock_gname t) ∅ with "[$]") as "?"; first set_solver.
    iModIntro.
    rewrite (left_id_L _ (∪)).
    go.
  Qed.

  (* Instance: `{ShouldInlineFunction n} | 1000 := {}. *)
  cpp.spec "C::one_answer()" from source inline.

  (* cpp.spec "C::~C()" from source inline. *)
  cpp.spec "C::~C()" from source as C_dtor_spec with (
    \this this
    \persist{thr} current_thread thr
    \pre{γ} this |-> CR γ 1$m
    \pre recursive_mutex.token (lock_gname γ) 1
    \pre recursive_mutex.used_threads (lock_gname γ) empty
    (* Currently unused, but callers are likely to have this and need to leak it. *)
    (* \pre recursive_mutex.locked (lock_gname γ) thr 0 *)

    (* **
      token (lock_gname γ) 1 **
      used_threads (lock_gname γ) {[thr]} **
      locked (lock_gname γ) thr 0 *)
    \post emp).

  (* #[global] Instance: Inhabited [tele _ : Z]. Proof. solve_inhabited. Qed. *)

  Lemma C_dtor_ok :
    (* We only get [|> recursive_mutex.dtor_spec'], and that's not enough *)
    recursive_mutex.dtor_spec' |--
    verify[source] "C::~C()".
  Proof.
    verify_spec.
    wuntil (wp_destroy_val _ _ _ (this ,, _field "C::value")) go.
    iApply fupd_wp_destroy_val.
    wname [bi_later] ">?"; iModIntro; go.

    destruct t as [? []]; rewrite P.unlock; go.

    (* _now_ we just need to leak ghost state and that's okay *)
    (* wname [recursive_mutex.locked] "L". *)
    (* iApply (affine with "L"). *)
    (* apply mpred_BiAffine. *)
  Qed.

  cpp.spec "ghost()" from source as ghost_spec with (
    \pre{P}
     |={⊤}=>
    P
    \post P).

  Lemma test_one_answer_ok :
    verify[source] "test_one_answer()".
  Proof.
    verify_spec; go.
    wname [recursive_mutex.locked (lock_gname t) thr 0] "C".
    iAssert (recursive_mutex.acquireable (TT := TT) t thr recursive_mutex.NotHeld (P c_addr)) with "[C]" as "?". {
      by rewrite recursive_mutex.acquireable.unlock; iFrame.
    }
    go.
    rewrite P.unlock.
    destruct args as [a []]; simpl in *.
    go.

    iExists ?[K], (mk 42).
    go.
    iSplitL ""; first by go; iModIntro; go.
    go.
    have [? [??]] : exists a, n = 1%nat /\ recursive_mutex.acquire a (recursive_mutex.release (recursive_mutex.Held n (mk 42))). {
      Unset SsrIdents.
      rename _n_ into n0.
      Set SsrIdents.
      (* This step breaks abstractions, but we have taken the lock yet hints don't
      give us access to the resouce. *)
      assert (n0 = 0 /\ n = 1)%nat as [-> ->]. {
        rewrite-> recursive_mutex.release.unlock in *.
        destruct n0, n; naive_solver.
      }
      rewrite recursive_mutex.release.unlock /=.
      exists recursive_mutex.NotHeld.
      split; first done.
      typeclasses eauto with br_hints.
    }
    rewrite CR'.unlock.
    go.
    destruct args as [a1 []].
    go.
    have [Ha1 Hrel]: (a1 = 42 /\ recursive_mutex.release (recursive_mutex.Held n (mk a1)) = recursive_mutex.NotHeld). {
      rewrite-> recursive_mutex.release.unlock in *; naive_solver.
    }
    iExists ?[K], (mk a1); go.
    wname [recursive_mutex.used_threads] "U".
    iSplitL "U"; go. {
      rewrite recursive_mutex.acquireable.unlock /=.
      work.
      rewrite -{1}(left_id_L ∅ (∪) {[thr]}) {}Hrel.
      iMod (recursive_mutex.logout with "[$]") as "[? ?]"; first set_solver.
      iModIntro.
      work.
    }
    rewrite P.unlock CR'.unlock; go.
    iApply affine; [apply mpred_BiAffine|go].
  Qed.

  (* TODO: when we project out equalities about Held and NotHeld, project info
  about the holding counts; that cancels out better when we repeatedly lock and
  unlock things. *)

  Lemma test_other_answer_ok :
    verify?[source] "test_other_answer()".
  Proof.
    verify_spec; go.
  Admitted.

  (* WIP, feel free to discard. *)
  (*
  cpp.spec "C::other_answer()" from source with (
    \this this
    (* \pre *)
    \pre{K} do_lock c g K
    \post K
  ).
  *)

End with_cpp.
