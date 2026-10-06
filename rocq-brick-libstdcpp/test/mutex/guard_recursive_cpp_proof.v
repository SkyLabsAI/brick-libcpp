(** Provisional *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
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
Succeed Definition b := std_recursive_mutex.Held 0 (mk 0).

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
  `{!std_recursive_mutex.G Σ}
  (γ : std_recursive_mutex.gname) (q : cQp.t) :=
  structR "C" q **
  as_Rep (fun this : ptr =>
    this ,, _field "C::m" |-> std_recursive_mutex.R γ q
      (∃ a : tele_arg TT, tele_app (P this) a)).

#[only(cfractional,ascfractional,cfracvalid,type_ptr)] derive CR.
#[only(lazy_unfold(export))] derive CR.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} {HAS_THREADS : HasStdThreads Σ}.

  Context `{!std_recursive_mutex.G Σ}.

  #[local] Instance: `{Objective1 (tele_app (P p))}.
  Proof. Admitted.

  #[global] Instance P_timeless p a : Timeless (P p a).
  Proof. rewrite P.unlock; apply _. Qed.

  Succeed #[global] Instance CR'_timeless' p args : Timeless (tele_app (TT := TT) (λ a : Z, p |-> CR' a) args) := _.
  Succeed #[global] Instance P_timeless' p args : Timeless (tele_app (P p) args) := _.

  cpp.spec "test_one_answer()" from source with (
    \persist{thr} current_thread thr
    \prepost{pool} MutexSets.my_mutexes pool thr (coPset.CoPset ⊤)
    \post[Vint 42] emp
  ).
  cpp.spec "test_other_answer()" from source with (
    \persist{thr} current_thread thr
    \prepost{pool} MutexSets.my_mutexes pool thr (coPset.CoPset ⊤)
    \post[Vint 42] emp
  ).

  (** Initialize the member lock but do not acquire it. *)
  cpp.spec "C::C()" from source as C_ctor_spec with (
    \this this
    \pre{pool N} emp
    \post Exists γ,
      [| std_recursive_mutex.pool_name γ = pool /\
         std_recursive_mutex.rmutex_inv_namespace γ = N |] **
      this |-> CR γ 1$m ** std_recursive_mutex.token γ 1$m
  ).

  (** XXX Does not appear to help *)
  #[global] Instance unfold (p' : ptr) : `{AutoUnlocking.DefinedUsing (P p n) (p' |-> CR' n')} := {}.

  Lemma C_ctor_ok :
    verify[source] "C::C()".
  Proof.
    verify_shift.
    go.
    iExists pool, N, TT, (P this), (mk 0); go.
    rewrite (* Ugh *) -bi.later_intro.
    rewrite {1}P.unlock.
    go.

    iModIntro. go.
  Qed.

  cpp.spec "C::~C()" from source as C_dtor_spec with (
    \this this
    \pre{γ} this |-> CR γ 1$m
    \pre std_recursive_mutex.token γ 1$m
    \post emp).

  Lemma C_dtor_ok :
    (* We only get [|> std_recursive_mutex.std_dtor_spec], and that's not enough *)
    std_recursive_mutex.std_dtor_spec |-- verify[source] "C::~C()".
  Proof.
    verify_shift; go.
    iModIntro. go.
    progress destruct_tele; rewrite P.unlock /=.
    go.
  Qed.

  cpp.spec "C::one_answer()" from source inline.

  Lemma test_one_answer_ok :
    verify[source] "test_one_answer()".
  Proof.
    verify_spec; go.
    iExists pool, (nroot .@@ "guard_recursive"); go.
    iDestruct (MutexSets.my_mutexes_alloc_mutex_name
      (std_recursive_mutex.pool_name t) thr ⊤
      (↑std_recursive_mutex.rmutex_inv_namespace t) ltac:(set_solver)
      with "[$]") as "[Hrest Hname]".
    wname [std_recursive_mutex.token] "Htoken".
    iAssert (std_recursive_mutex.acquireable (c_addr ,, _field "C::m")
      (TT := TT) t 1$m thr std_recursive_mutex.NotHeld (P c_addr))%I
      with "[Htoken Hname]" as "Hacquireable".
    { rewrite /std_recursive_mutex.acquireable /=
        -std_recursive_mutex.register_thread. iFrame "#∗". }
    iDestruct "Hacquireable" as "?". go.
    destruct args as [a []].
    rewrite P.unlock /=.
    go.

    iExists ?[K], (mk 42). go.
    iSplitL ""; [by go | go].
    have [? [??]] : exists a, n = 1%nat /\ std_recursive_mutex.acquire a (std_recursive_mutex.release (std_recursive_mutex.Held n (mk 42))). {
      lazymatch goal with
      | _ : std_recursive_mutex.Held ?x _ = _ |- _ => rename x into n0
      end.
      (* This step breaks abstractions, but we have taken the lock yet hints don't
      give us access to the resouce. *)
      assert (n0 = 0 /\ n = 1)%nat as [-> ->]. {
        rewrite-> std_recursive_mutex.release.unlock in *.
        destruct n0, n; naive_solver.
      }
      rewrite std_recursive_mutex.release.unlock /=.
      exists std_recursive_mutex.NotHeld.
      split; first done.
      typeclasses eauto with br_hints.
    }
    go.
    rewrite CR'.unlock.
    destruct args as [a1 []].
    go.
    have [Ha1 Hrel]: (a1 = 42 /\ std_recursive_mutex.release (std_recursive_mutex.Held n (mk a1)) = std_recursive_mutex.NotHeld). {
      rewrite-> std_recursive_mutex.release.unlock in *; naive_solver.
    }
    subst a1.
    iExists ?[K], (mk 42). rewrite Hrel /=.
    go.
    iSplitL ""; [by go | go].
    rewrite P.unlock CR'.unlock; go.
    match goal with g : std_recursive_mutex.gname |- _ => rename g into γ end.
    iDestruct select (std_recursive_mutex.acquireable _ _ _ _ _ _) as "Hacquireable".
    iEval (rewrite /std_recursive_mutex.acquireable /=
      -std_recursive_mutex.register_thread) in "Hacquireable".
    iDestruct "Hacquireable" as "(_ & Htoken & Hname)".
    iDestruct (MutexSets.my_mutexes_join_mutex_name
      (std_recursive_mutex.pool_name γ) thr ⊤
      (↑std_recursive_mutex.rmutex_inv_namespace γ) ltac:(set_solver)
      with "[Hrest Hname]") as "Hnames"; first iFrame.
    iFrame "Htoken". go $usenamed=true.
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
