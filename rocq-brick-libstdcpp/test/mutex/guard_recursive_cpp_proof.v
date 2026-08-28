(** Provisional *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.test.mutex.guard_recursive_cpp.

Import linearity.

(** TO UPSTREAM START *)
#[global] Hint Extern 100 (tforall _) => cbn : typeclass_instances.
Existing Class tforall.

Section to_upstream.
  #[global] Instance TeleS_inhabited {X : Type} {binder : X → tele} :
    (∀ x : X, Inhabited (binder x)) →
    Inhabited X ->
    Inhabited (TeleS binder).
  Proof. unshelve solve_inhabited. solve_inhabited. Qed.

  #[global] Instance timeless_tele_app {PROP : bi} {TT : tele} (args : TT) (P : TT -t> PROP):
    `{(∀.. args, Timeless (tele_app P args)) -> Timeless (tele_app P args)}.
  Proof.
    elim: TT args P => [[] //|T TT IH] args P HT.
    destruct_tele; simpl.
    apply IH, HT.
  Qed.

  #[program]
  Definition strip_timeless_later_is_except_CX {PROP : bi} :=
    \cancelx
    \consuming{P : PROP} ▷ P
    \guard Timeless P
    \guard{Q} IsExcept0 Q
    \proving Q
    \through P -* Q
    \end.
  Next Obligation. intros. iIntros ">? ?". work. Qed.

  Section wp_destroy_val.
    Context `{Σ : cpp_logic, σ : genv}.
    Context {tu : translation_unit} (cv : type_qualifiers) (ty : type) (p : ptr).

    #[local] Abbreviation WP := (wp_destroy_val tu cv ty p) (only parsing).

    #[global] Instance elim_modal_fupd_wp_destroy_val b P Q :
      ElimModal True b false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_destroy_val.
    Qed.

    #[global] Instance wp_destroy_val_is_except_0 Q: IsExcept0 (WP Q).
    Proof.
      rewrite /IsExcept0 -{2}fupd_wp_destroy_val. by iIntros ">$ !>".
    Qed.
  End wp_destroy_val.
End to_upstream.

#[global] Hint Resolve strip_timeless_later_is_except_CX : br_hints.
Add Auto Subgoal IsExcept0.
(** TO UPSTREAM END *)

Implicit Type (p : ptr) (σ : genv).

Abbreviation TT := [tele (_ : Z)].
Succeed #[global] Instance: Inhabited TT := _.

(** Canonical "constructor" for our telescope. *)
Polymorphic Definition mk (a : Z) : TT :=
  {| tele_arg_head := a; tele_arg_tail := () |}.
Succeed Definition b := recursive_mutex.Held 0 (mk 0).

sl.lock
Definition CR' `{Σ : cpp_logic, σ : genv} (a : Z) : Rep :=
  _field "C::value" |-> intR 1$m a.
#[only(lazy_unfold(export))] derive CR'.
#[only(timeless)] derive CR'.

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
  _field "C::m" |-> recursive_mutex.derivedR γ q **
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

  Succeed #[global] Instance CR'_timeless' p args : Timeless (tele_app (TT := TT) (λ a : Z, p |-> CR' a) args) := _.
  Succeed #[global] Instance P_timeless' p args : Timeless (tele_app (P p) args) := _.

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
      recursive_mutex.used_threads (lock_gname γ) {[thr]} **
      recursive_mutex.acquireable (TT := TT) γ thr recursive_mutex.NotHeld (P this)
  ).

  (** XXX Does not appear to help *)
  #[global] Instance unfold (p' : ptr) : `{AutoUnlocking.DefinedUsing (P p n) (p' |-> CR' n')} := {}.

  Lemma C_ctor_ok :
    verify[source] "C::C()".
  Proof.
    verify_shift; go.
    iExists TT, (P this), (mk 0); go.
    rewrite (* Ugh *) -bi.later_intro.
    rewrite {1}P.unlock.
    go.

    iMod (recursive_mutex.use_thread thr (lock_gname t) ∅ with "[$]") as "?"; first set_solver; iModIntro.
    go.
    rewrite recursive_mutex.acquireable.unlock (left_id_L _ (∪)).
    go.
  Qed.

  cpp.spec "C::~C()" from source as C_dtor_spec with (
    \this this
    \persist{thr} current_thread thr
    \pre{γ} this |-> CR γ 1$m
    (* \pre recursive_mutex.used_threads (lock_gname γ) empty *)
    \pre recursive_mutex.used_threads γ.(lock_gname) {[thr]}
    \pre recursive_mutex.inv_rmutex γ (∃ xs, tele_app (TT := TT) (P this) xs)
    \pre recursive_mutex.acquireable (TT := TT) γ thr recursive_mutex.NotHeld (P this)
    \post emp).

  Lemma C_dtor_ok :
    (* We only get [|> recursive_mutex.dtor_spec'], and that's not enough *)
    recursive_mutex.dtor_spec' |-- verify[source] "C::~C()".
  Proof.
    verify_shift; go.
    wapply (recursive_mutex.logout thr _ ∅); first by set_solver.
    rewrite recursive_mutex.acquireable.unlock /= (left_id_L _ (∪)).
    go with br_erefl.
    iModIntro.
    go.
    progress destruct_tele; rewrite P.unlock /=.
    go.
    iApply affine; [apply mpred_BiAffine|go].
  Qed.

  cpp.spec "C::one_answer()" from source inline.

  Lemma test_one_answer_ok :
    verify[source] "test_one_answer()".
  Proof.
    verify_spec; go.
    destruct args as [a []].
    rewrite P.unlock /=.
    go.

    iExists ?[K], (mk 42). go.
    iSplitL ""; [by go | go].
    have [? [??]] : exists a, n = 1%nat /\ recursive_mutex.acquire a (recursive_mutex.release (recursive_mutex.Held n (mk 42))). {
      lazymatch goal with
      | _ : recursive_mutex.Held ?x _ = _ |- _ => rename x into n0
      end.
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
    go.
    rewrite CR'.unlock.
    destruct args as [a1 []].
    go.
    have [Ha1 Hrel]: (a1 = 42 /\ recursive_mutex.release (recursive_mutex.Held n (mk a1)) = recursive_mutex.NotHeld). {
      rewrite-> recursive_mutex.release.unlock in *; naive_solver.
    }
    subst a1.
    iExists ?[K], (mk 42). rewrite Hrel /=.
    go.
    iSplitL ""; [by go | go].
    rewrite P.unlock CR'.unlock; go.
  Qed.

  (* TODO: when we project out equalities about Held and NotHeld, project info
  about the holding counts; that cancels out better when we repeatedly lock and
  unlock things. *)

  Lemma test_other_answer_ok :
    verify?[source] "test_other_answer()".
  Proof.
    verify_spec; go.
  Abort.

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
