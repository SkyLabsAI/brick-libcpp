(** A finite pool of the existing shared-pointer acquisition tokens.
    Credits account for available tokens; the persistent invariant alone does
    not authorize a copy. These lemmas use ghost-state rules, not the assumed
    C++ constructor or destructor specs. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.invariants.
Require Import skylabs.base_logic.lib.own_auth.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import iris.algebra.auth iris.algebra.numbers.
Require Import skylabs.iris.extra.bi.algebra.
Require Import skylabs.iris.extra.proofmode.own_obs.

Set Default Goal Selector "!".
#[local] Set Warnings "+sl-transparent-constants".
Import linearity.
#[local] Hint Opaque SharedPtrR : sl_opacity.

Module TokenPool.
Section pool.
  Context `{Sigma : cpp_logic}.
  #[local] Existing Instances br.ghost.auth_nat_inG br.ghost.excl_inG.

  Definition valid_indices (id : CtrlBlockId) (indices : gset nat) : Prop :=
    forall i, i ∈ indices ->
      (i < length (pieceRightLocs id))%nat /\
      (N.of_nat i < N.pos maxContention)%N.

  Definition credits (gamma : gname) (n : nat) : mpred :=
    own gamma (◯ n : authR natUR).

  Definition pool_body (gamma : gname) (id : CtrlBlockId)
      (indices : gset nat) : mpred :=
    Exists free : gset nat,
      [| free ⊆ indices |] **
      own gamma (● size free : authR natUR) **
      [∗ set] i ∈ free, pieceRight id i.

  Definition pool (ns : namespace) (gamma : gname) (id : CtrlBlockId)
      (indices : gset nat) : mpred :=
    [| valid_indices id indices |] ** inv ns (pool_body gamma id indices).

  #[local] Hint Opaque pool pool_body credits pieceRight : sl_opacity.

  #[global] Instance pool_persistent ns gamma id indices :
    Persistent (pool ns gamma id indices) := _.

  #[global] Instance pool_body_timeless gamma id indices :
    Timeless (pool_body gamma id indices).
  Proof.
    unfold pool_body, pieceRight.
    apply _.
  Qed.

  Lemma credits_add gamma n m :
    credits gamma (n + m) -|- credits gamma n ** credits gamma m.
  Proof.
    unfold credits.
    exact (own_op gamma (◯ n : authR natUR) (◯ m)).
  Qed.

  Lemma credits_zero gamma : emp |-- (|==> credits gamma 0)%I.
  Proof.
    exact (own_unit (PROP := mpredI) (A := authUR natUR) gamma).
  Qed.

  Lemma pieceRight_exclusive id i :
    (i < length (pieceRightLocs id))%nat ->
    pieceRight id i ** pieceRight id i |-- False.
  Proof.
    intros Hbound.
    unfold pieceRight.
    destruct (nth_error (pieceRightLocs id) i) as [name |] eqn:Hlookup.
    {
      rewrite <- own_op, own_valid, excl_op_validI.
      reflexivity.
    }
    {
      apply nth_error_None in Hlookup.
      lia.
    }
  Qed.

  #[local] Instance counter_bound gamma available used :
    Observe2 [| (used <= available)%nat |]
      (own gamma (● available : authR natUR)) (credits gamma used).
  Proof.
    unfold credits.
    rewrite <- (nat_included used available).
    exact (auth_both_included' gamma 1 available used).
  Qed.

  Lemma counter_take gamma available k :
    (S k <= available)%nat ->
    own gamma (● available : authR natUR) ** credits gamma (S k)
    |-- (|==> own gamma (● (Nat.pred available) : authR natUR) **
              credits gamma k)%I.
  Proof.
    intros Hbound.
    unfold credits.
    rewrite <- !own_op.
    apply own_update.
    apply auth_update, nat_local_update.
    lia.
  Qed.

  Lemma counter_return gamma available :
    own gamma (● available : authR natUR)
    |-- (|==> own gamma (● (S available) : authR natUR) ** credits gamma 1)%I.
  Proof.
    unfold credits.
    rewrite <- own_op.
    apply own_update, auth_update_alloc, nat_local_update.
    change (available + 1 = S available + 0)%nat.
    lia.
  Qed.

  Lemma alloc E ns id indices :
    valid_indices id indices ->
    ([∗ set] i ∈ indices, pieceRight id i)
    |-- (|={E}=> Exists gamma,
        pool ns gamma id indices ** credits gamma (size indices))%I.
  Proof.
    intros Hvalid.
    rewrite <- bi.emp_sep at 1.
    etrans.
    {
      apply bi.sep_mono_l.
      exact (own_alloc_auth (A := natUR) (size indices) ltac:(done)).
    }
    eapply useBupdS.
    go.
    rewrite <- fupd_exist.
    iExists t.
    unfold pool, credits.
    rewrite <- fupd_frame_r.
    go.
    rewrite <- fupd_frame_l.
    go.
    assert (WeaklyObjective (pool_body t id indices)).
    { unfold pool_body, pieceRight. apply _. }
    wapply (inv_alloc ns E (pool_body t id indices)).
    rewrite <- fupd_intro.
    go.
    unfold pool_body.
    rewrite <- bi.later_intro.
    rewrite bi.sep_exist_r.
    iExists indices.
    assert (indices ⊆ indices) by reflexivity.
    go.
  Qed.

  Lemma take_body E gamma id indices k :
    pool_body gamma id indices ** credits gamma (S k)
    |-- (|={E}=> pool_body gamma id indices ** credits gamma k **
        (Exists i, [| i ∈ indices |] ** pieceRight id i))%I.
  Proof.
    unfold pool_body at 1.
    go.
    rename t into free.
    wapply (observe_2_uncurry_elim [| (S k <= size free)%nat |]
      (own gamma (● size free : authR natUR)) (credits gamma (S k))).
    go.
    assert (Hnonempty : free <> ∅).
    { intros ->. rewrite size_empty in H. lia. }
    destruct (set_choose_L free Hnonempty) as [i Hi].
    wapply (counter_take gamma (size free) k H).
    go.
    rewrite <- fupd_intro.
    iExists i.
    rewrite (big_sepS_delete _ free i Hi).
    assert (i ∈ indices) by set_solver.
    unfold pool_body.
    rewrite bi.sep_exist_r.
    iExists (free ∖ {[i]}).
    assert (free ∖ {[i]} ⊆ indices) by set_solver.
    rewrite size_difference; last set_solver.
    rewrite size_singleton.
    replace (size free - 1)%nat with (Nat.pred (size free)) by lia.
    go.
  Qed.

  Lemma return_body E gamma id indices i :
    valid_indices id indices -> i ∈ indices ->
    pool_body gamma id indices ** pieceRight id i
    |-- (|={E}=> pool_body gamma id indices ** credits gamma 1)%I.
  Proof.
    intros Hvalid Hi.
    unfold pool_body at 1.
    go.
    rename t into free.
    destruct (decide (i ∈ free)) as [Hin | Hout].
    {
      rewrite (big_sepS_delete _ free i Hin).
      wapply (pieceRight_exclusive id i (proj1 (Hvalid i Hi))).
      go.
    }
    {
      wapply (counter_return gamma (size free)).
      go.
      rewrite <- fupd_intro.
      unfold pool_body.
      rewrite bi.sep_exist_r.
      iExists ({[i]} ∪ free).
      assert ({[i]} ∪ free ⊆ indices) by set_solver.
      rewrite size_union; last set_solver.
      rewrite size_singleton /=.
      rewrite big_sepS_insert; last done.
      go.
    }
  Qed.

  (** Both public operations restore the caller's mask: the invariant is never
      held open while a C++ constructor or destructor runs. *)
  Lemma take E ns gamma id indices k :
    ↑ns ⊆ E ->
    pool ns gamma id indices ** credits gamma (S k)
    |-- (|={E}=> credits gamma k **
        (Exists i, [| i ∈ indices |] ** pieceRight id i))%I.
  Proof.
    intros Hmask.
    unfold pool.
    go.
    wapply (inv_acc_timeless E ns (pool_body gamma id indices) Hmask).
    go.
    wapply (take_body (E ∖ ↑ns) gamma id indices k).
    go.
    wapply (bi.wand_elim_l (pool_body gamma id indices)
      (|={E ∖ ↑ns,E}=> emp)%I).
    go.
    rewrite <- fupd_intro.
    iExists t.
    go.
  Qed.

  Lemma put E ns gamma id indices i :
    ↑ns ⊆ E -> i ∈ indices ->
    pool ns gamma id indices ** pieceRight id i
    |-- (|={E}=> credits gamma 1)%I.
  Proof.
    intros Hmask Hi.
    unfold pool.
    go.
    wapply (inv_acc_timeless E ns (pool_body gamma id indices) Hmask).
    go.
    wapply (return_body (E ∖ ↑ns) gamma id indices i H Hi).
    go.
    wapply (bi.wand_elim_l (pool_body gamma id indices)
      (|={E ∖ ↑ns,E}=> emp)%I).
    go.
    rewrite <- fupd_intro.
    go.
  Qed.

  Lemma excess_credits E ns gamma id indices :
    ↑ns ⊆ E ->
    pool ns gamma id indices ** credits gamma (S (size indices))
    |-- (|={E}=> False)%I.
  Proof.
    intros Hmask.
    unfold pool.
    go.
    wapply (inv_acc_timeless E ns (pool_body gamma id indices) Hmask).
    go.
    unfold pool_body.
    go.
    rename H into Hsubset.
    wapply (observe_2_uncurry_elim [| (S (size indices) <= size free)%nat |]
      (own gamma (● size free : authR natUR))
      (credits gamma (S (size indices)))).
    go.
    exfalso.
    pose proof (subseteq_size free indices Hsubset).
    lia.
  Qed.

  (** Reserving a token and cancelling that reservation preserves the budget.
      This is not a C++ copy/destruction proof: those operations must establish
      the separate outstanding-piece protocol described by their specs. *)
  Lemma reservation_round_trip E ns gamma id indices k :
    ↑ns ⊆ E ->
    pool ns gamma id indices ** credits gamma (S k)
    |-- (|={E}=> credits gamma (S k))%I.
  Proof.
    intros Hmask.
    wapply (take E ns gamma id indices k Hmask).
    go.
    wapply (put E ns gamma id indices t Hmask H).
    go.
    rewrite <- fupd_intro.
    replace (S k) with (k + 1)%nat by lia.
    rewrite credits_add.
    go.
  Qed.
End pool.
End TokenPool.
