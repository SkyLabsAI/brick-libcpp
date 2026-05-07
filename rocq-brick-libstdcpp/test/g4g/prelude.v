Require Export skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.iostream.spec.

Require Export skylabs.iris.extra.base_logic.lib.spectra.

(* BEGIN UPSTREAM *)

(* FOR SPECTRA definition *)
Class appG {evt : Type} (lts : LTS evt) (Σ : gFunctors) : Type :=
{ _has_auth_set_state : inG Σ (auth_setR (lts_state lts)) }.

Section to_spectra.
  Context `{Σ : cpp_logic}.

  #[program]
  Definition mkApp {event} (APP : LTS event) {SPECTRA : appG APP _Σ} : App.app :=
    {| App.evt := event
    ; App.lts := APP
    ; App.inG := _
    |}.
  Next Obligation.
    intros. unshelve eapply mpred_prop.mpred_has_usual_own. apply SPECTRA.
  Defined.
End to_spectra.

Section to_tele.
  Lemma tele_snoc_arg_snoc {TT T} (x : tele_snoc TT T) : exists ys y,
      x = tele_arg_snoc ys y.
  Proof.
    clear.
    induction TT; simpl in *.
    { destruct x. exists tele_arg_tail, tele_arg_head. destruct tele_arg_tail. done. }
    { destruct x.
      destruct (H tele_arg_head tele_arg_tail) as [?[??]].
      subst. exists (TeleArgCons (f:=fun _ => _) tele_arg_head x), x0. done. }
  Qed.
  Lemma tele_app_bind_snoc {TT : tele} T U (x : T) : forall (xs : TT) (f : _ -> _ -> U),
      tele_app (tele_bind_snoc f) (tele_arg_snoc xs x) = f xs x.
  Proof.
    clear. induction TT; intros.
    { destruct xs; done. }
    { destruct xs. etrans. apply H. done. }
  Qed.
End to_tele.

Section to_auto.
  Context {PROP : bi}.
  #[program]
  Definition pick_ex_C {PROP:bi}:=
    \cancelx
    \bound_existential Q
    \proving{P} (P -∗ Q)
    \instantiate Q := P
    \end@{PROP}.
  Next Obligation.
    intros.
    iIntros "_" (??? ->). iIntros "$".
  Qed.
End to_auto.
#[global] Hint Resolve pick_ex_C | 200 : sl_opacity.

Section to_cpp_auto.
  Context `{Σ : cpp_logic} {σ : genv}.
  #[program]
  Definition spec_lookup_C {fn iSpec}  :=
    \cancelx
    \preserving{P (_ : find_spec.FindSpec _ false (_global fn) P iSpec)} □ P
    \proving{spec} _global fn |-> cptrR spec
    \through [| spec = iSpec |]
    \end.
  Next Obligation.
    intros.
    iIntros "#P" (??); subst.
    destruct H.
    iDestruct (_spec_ok with "P") as "#$".
  Qed.
End to_cpp_auto.
#[global] Hint Resolve spec_lookup_C | 200 : sl_opacity.

(* FOR SPECTRA automation *)
Section operational.
  Context {T E} (step : T -> option E -> T -> Prop).

  Class AnyStep  (Pre : propset T) (evt : E) (Post : propset T) : Prop :=
  { _safe : forall s, s ∈ Pre -> exists s', step s (Some evt) s' /\ s' ∈ Post
  ; _steps_to : forall s', s' ∈ Post -> ∃ s, s ∈ Pre /\ step s (Some evt) s' }.


  Inductive AnySteps (Pre : propset T) : list E -> propset T -> Prop :=
  | Finish {Post} {_ : ∅ ⊂ Post} (_ : Post ⊆ Pre) : AnySteps Pre [] Post
  | Step {evt evts Mid Post}
      (_ : AnyStep Pre evt Mid)
      (_ : AnySteps Mid evts Post)
    : AnySteps Pre (evt :: evts) Post
  | Refine {Pre'} {_ : ∅ ⊂ Pre} (_ : Pre' ⊆ Pre) {es Post} :
    AnySteps Pre' es Post -> AnySteps Pre es Post.

  Lemma AnySteps_mono_post Pre evts Post Post' :
    ∅ ⊂ Post' ⊆ Post ->
    AnySteps Pre evts Post ->
    AnySteps Pre evts Post'.
  Proof.
    induction 2; eauto using AnySteps.
    constructor; set_solver.
  Qed.

  Lemma AnySteps_mono_pre Pre Pre' evts Post :
    (* ∅ ⊂ Pre' ⊆ Pre ->
    AnySteps Pre evts Post ->
    AnySteps Pre' evts Post. *)
    ∅ ⊂ Pre ->
    Pre' ⊆ Pre ->
    AnySteps Pre' evts Post ->
    AnySteps Pre evts Post.
  Proof. intros. exact: Refine. Qed.

  Lemma AnyStep_invert_nonempty Pre evt Post :
    AnyStep Pre evt Post ->
    ∅ ⊂ Post <-> ∅ ⊂ Pre.
  Proof. intros []; set_solver. Qed.

  Lemma AnySteps_invert_nonempty Pre evts Post :
    AnySteps Pre evts Post ->
    ∅ ⊂ Post /\ ∅ ⊂ Pre.
  Proof.
    induction 1; intuition.
    - set_solver.
    - by rewrite -AnyStep_invert_nonempty.
  Qed.
End operational.
Existing Class AnySteps.
#[global] Hint Mode AnyStep + + + + + - : typeclass_instances.
#[global] Hint Mode AnySteps + + + + + - : typeclass_instances.


Section to_spectra.
  Context {PROP : bi}.
  Context {HAS_FUPD : BiFUpd PROP} {GHOSTLY : prop_constraints.Ghostly PROP}.
  Context `{SPECTRA : @appG evt lts Σ}.


  #[global] Instance requester_frame' T app E γ ps (F : (T -t> PROP) -> [tele (_:App.evt app)] -t> PROP)
 :
    (forall x, kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => F K x)) ->
    kont.ProperFrame (PROP:=PROP) (T:=T) (fun K => Step.requester app E γ ps (F K)).
  Proof.
    intros.
    constructor.
    iIntros (??) "K H".
    rewrite /Step.requester.
    iApply (atomic_commit_ppost_wand with "[H]") => //.
    simpl.
    iIntros (? e); destruct (H e).
    iApply _frame. done.
  Qed.

  Context {T : Type} {HAS_OWN : prop_constraints.HasUsualOwn PROP (auth_setR T)}.
  Lemma frag_frag_exact  γ val :
    AuthSet.frag γ {[ val ]} ⊣⊢@{PROP} AuthSet.frag_exact γ val.
  Proof. reflexivity. Qed.
  Definition frag_frag_exact_F := [FWD<-] @frag_frag_exact.
  Definition frag_frag_exact_B := [BWD<-] @frag_frag_exact.

  #[global]
  Instance authset_frag_exact_learn {γ} :
    Cbn (Learn (learn_eq ==> learn_hints.fin) (fun x => AuthSet.frag γ {[x]})).
  Proof. clear. solve_learnable. Qed.
  Hint Resolve authset_frag_exact_learn : sl_opacity.


  (* The early commit version
  #[program]
  Definition requester_ec_C (app : App.app) (s : _) s' evt :=
    \cancelx
    \using{γ} AuthSet.frag γ {[s]}
    \proving{E K} Step.requester app E γ {[ evt ]} K
    \through{s'} [| AnyStep app.(App.lts).(Sts._step) {[s]} evt s' |]
    \through AuthSet.frag γ s' -∗ K evt
    \end@{mpredI}.
  Next Obligation. Abort.
  *)

  #[program]
  Definition requester_C {_ : BiBUpdFUpd PROP} (app : App.app) (s : _) s' evt
    (ANY_STEP : AnyStep app.(App.lts).(Sts._step) {[s]} evt s'):=
    \cancelx
    \using{γ} AuthSet.frag γ {[s]}
    \proving{E K} Step.requester app E γ {[ evt ]} K
    \through AuthSet.frag γ s' -∗ K evt
    \end@{PROP}.
  Next Obligation.
    intros.
    work.
    rewrite /Step.requester.
    iAcIntro.
    rewrite /commit_acc.
    simpl.
    iApply fupd_mask_intro; [ by set_solver | ].
    iIntros "Hclose".
    work.
    iExists s.
    rewrite /AuthSet.frag_exact. work.
    iSplitR.
    { iPureIntro.
      intros. destruct ANY_STEP.
      inversion H; subst. apply _safe0. done. }
    iIntros (?) "[% Hfrag]". iMod "Hclose".
    work.
    iApply bupd_fupd.
    iDestruct (AuthSet.frag_upd with "Hfrag") as ">Hfrag"; last by iModIntro; iFrame.
    inversion ANY_STEP.
    inversion H; subst; clear H.
    intros ? Hin. apply _steps_to0 in Hin.
    inversion Hin as [?[??]].
    inversion H; subst. done.
  Qed.
  Hint Resolve requester_C : sl_opacity.

  #[global]
  Instance requester_ne {app E γ} :
    forall n, Proper ((≡) ==> pointwise_relation _ (dist n) ==> dist n) (Step.requester app E γ).
  Proof.
    repeat intro.
    apply atomic_commit_ne => //; repeat intro;
                             repeat match goal with
                               | h : tele_arg _ |- _ => destruct h
                               end; simpl; repeat f_equiv; eauto.
    by setoid_rewrite H.
  Qed.

  (* NOTE: generalizing this over an [App.app] is difficult because [App.app] hides
     the event signature. *)
  #[program]
  Definition OS (APP: App.app) (E : coPset) γ : SepHandler PROP (App.evt APP) :=
    {| do evt K := Step.requester APP E γ evt K |}%I.

End to_spectra.
#[global] Hint Resolve frag_frag_exact_B frag_frag_exact_F : sl_opacity.

#[global]
Instance of_unmaterialized_refine1 `{Σ : cpp_logic} {σ : genv} {ty s s'}:
  Refine1 false true (unmaterialized_fspec ty s = unmaterialized_fspec ty s')
    [ s = s' ].
Proof.
  constructor; simpl; auto.
  inversion 1; subst; done.
Qed.

Section to_kont.
  Context {PROP : bi}.
  #[global]
  Instance as_sep_L_proper_frame {TT : tele} {P Q}
    : kont.AsSep P ->
      kont.ProperFrame (fun K : TT -t> PROP => P K ∗ Q)%I.
  Proof.
    destruct 1. constructor.
    iIntros (??) "K [P $]".
    rewrite !_as_sep.
    iDestruct "P" as (?) "[A B]".
    iExists _; iFrame "B". iApply "K"; iApply "A".
  Qed.

  #[global]
  Instance as_sep_R_proper_frame {TT : tele} {P Q}
    : kont.AsSep Q ->
      kont.ProperFrame (fun K : TT -t> PROP => P ∗ Q K)%I.
  Proof.
    destruct 1. constructor.
    iIntros (??) "K [$ P]".
    rewrite !_as_sep.
    iDestruct "P" as (?) "[A B]".
    iExists _; iFrame "B". iApply "K"; iApply "A".
  Qed.

  (* this instance is a bit of a bug when happen to end up
     finding [fun K => P ∗ K], then this can be eta-contracted to
     [bi_sep P].
   *)
  #[global]
  Instance hack_proper_frame {P}
    : kont.ProperFrame (PROP:=PROP) (T:=[tele]) (bi_sep P)%I.
  Proof.
    clear.
    constructor; simpl.
    iIntros (??) "K [$ P]".
    iApply ("K" $! ()). done.
  Qed.
End to_kont.
(* END UPSTREAM *)


(** The step relation for a simple LTS that uses [bs] as the state.

    This LTS only supports output transitions.
 *)
Inductive only_output : bs -> option output_event -> bs -> Prop :=
| output_char {c} {b : bs} : only_output (BS.String c b) (Some $ Write $ Byte.to_N c) b
| skip {bs} : only_output bs None bs.

#[global]
Instance only_output_any_step {c cs} : AnyStep only_output {[ BS.String c cs ]} (Write $ Byte.to_N c) {[ cs ]}.
Proof.
  constructor; inversion 1; subst.
  { eexists; constructor. }
  { eexists; repeat constructor. }
Qed.

#[global]
Instance final_any_steps {str str' : bs} :
  str = str' ->
  AnySteps only_output {[str]}
      ((λ x : N, Write x) <$> BS.string_to_bytes (str'))
      {[""%bs]}.
Proof.
  intros; subst.
  clear.
  induction str'.
  { constructor; set_solver. }
  { simpl.
    econstructor; [ | eassumption ].
    constructor.
    { intros. exists str'.
      inversion H; subst. constructor. }
    { inversion 1; subst.
      eexists _; split. set_solver.
      constructor. } }
Qed.

#[global]
Instance initial_any_steps {str str' rest : bs} :
  str = str' ->
  AnySteps only_output {[str ++ rest]}%bs
    ((λ x : N, Write x) <$> BS.string_to_bytes (str'))
    {[rest]}.
Proof.
  intros; subst.
  clear.
  revert rest.
  induction str'.
  { constructor; set_solver. }
  { simpl.
    econstructor; [ | eapply IHstr' ].
    { constructor.
      { intros. exists (str' ++ rest)%bs.
        inversion H; subst.
        have->: (BS.String b str' ++ rest = BS.String b (str' ++ rest))%bs by done.
        constructor. }
      { inversion 1; subst.
        eexists _; split. set_solver.
        constructor. } } }
Qed.

Definition output_app (init : bs -> Prop) : LTS output_event :=
  {| Sts._state := bs
   ; Sts._init_state := init
   ; Sts._step := only_output |}.
