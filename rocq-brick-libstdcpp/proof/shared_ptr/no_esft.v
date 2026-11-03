(** Exclusion of the payload mutation performed by enable_shared_from_this.
    The proposition requires complete inheritance information and excludes
    both public and internal enable_shared_from_this bases. The boolean search
    decides that proposition. Opaque, unsupported, and missing declarations
    are rejected rather than treated as evidence that a class has no bases. *)
Require Import skylabs.auto.cpp.proof.

Set Default Goal Selector "!".

Section hierarchy.
  Context {sigma : genv}.

  Definition esft_name_ok (cls : name) : bool :=
    match cls with
    | Ninst template _ =>
        bool_decide (template <> "std::enable_shared_from_this"%cpp_name /\
          template <> "std::__enable_shared_from_this"%cpp_name)
    | _ => true
    end.

  Lemma esft_name_ok_spec cls :
    esft_name_ok cls = true <->
    forall pack,
      cls <> Ninst "std::enable_shared_from_this" pack /\
      cls <> Ninst "std::__enable_shared_from_this" pack.
  Proof.
    destruct cls; simpl; try (split; [intros _ pack; split; discriminate | done]).
    rewrite bool_decide_eq_true.
    split.
    { intros [Hstd Hinternal] pack. split; congruence. }
    { intro H. destruct (H l) as [Hstd Hinternal]. split; congruence. }
  Qed.

  Definition esft_children (cls : name) : list name :=
    match glob_def sigma cls with
    | Some (Gstruct layout) => map fst layout.(s_bases)
    | _ => []
    end.

  Definition esft_node_ok (cls : name) : bool :=
    match glob_def sigma cls with
    | Some (Gstruct _ | Gunion _ | Genum _ _) => esft_name_ok cls
    | _ => false
    end.

  Definition esft_class_safe (cls : name) : Prop :=
    forall base, rtc (fun parent child => child ∈ esft_children parent) cls base ->
      esft_node_ok base = true.

  Definition shared_ptr_no_esft (ty : type) : Prop :=
    match erase_qualifiers ty with
    | Tnamed cls => esft_class_safe cls
    | _ => True
    end.

  Lemma esft_safe_node cls : esft_class_safe cls -> esft_node_ok cls = true.
  Proof.
    intros Hsafe. apply Hsafe. constructor.
  Qed.

  Lemma esft_safe_children cls :
    esft_class_safe cls -> List.Forall esft_class_safe (esft_children cls).
  Proof.
    intros Hsafe. apply Forall_forall. intros base Hbase node Hpath.
    apply Hsafe. econstructor; eauto.
  Qed.

  Lemma esft_closed_safe (done : list name) :
    List.Forall (fun cls => esft_node_ok cls = true) done ->
    (forall cls, cls ∈ done -> forall base, base ∈ esft_children cls -> base ∈ done) ->
    forall cls, cls ∈ done -> esft_class_safe cls.
  Proof.
    intros Hnodes Hclosed cls Hin base Hpath. revert Hin.
    induction Hpath as [node | parent child node Hedge Hpath IH]; intros Hin.
    { exact (proj1 (Forall_forall _ _) Hnodes node Hin). }
    apply IH. eapply Hclosed; eauto.
  Qed.

  (** Each declared class contributes its outgoing base edges at most once.
      The initial work item plus all those edges therefore bounds queue pops,
      including duplicates and cycles. *)
  Definition esft_edge_cost (seen : list name) (entry : name * GlobDecl) : nat :=
    if bool_decide (entry.1 ∈ seen) then 0 else
      match entry.2 with
      | Gstruct layout => length layout.(s_bases)
      | _ => 0
      end.

  Definition esft_remaining_edges (seen : list name) : nat :=
    list_sum (map (esft_edge_cost seen) (map_to_list sigma.(genv_tu).(types))).

  Lemma esft_edge_cost_mono seen cls entry :
    esft_edge_cost (cls :: seen) entry <= esft_edge_cost seen entry.
  Proof.
    unfold esft_edge_cost. repeat case_bool_decide; try set_solver; lia.
  Qed.

  Lemma esft_edge_sum_mono seen cls entries :
    list_sum (map (esft_edge_cost (cls :: seen)) entries) <=
    list_sum (map (esft_edge_cost seen) entries).
  Proof.
    induction entries as [| entry entries IH]; simpl; first lia.
    pose proof (esft_edge_cost_mono seen cls entry). lia.
  Qed.

  Lemma esft_edge_sum_take seen cls layout entries :
    cls ∉ seen -> (cls, Gstruct layout) ∈ entries ->
    length layout.(s_bases) +
      list_sum (map (esft_edge_cost (cls :: seen)) entries) <=
      list_sum (map (esft_edge_cost seen) entries).
  Proof.
    intros Hfresh. induction entries as [| entry entries IH]; intros Hin.
    { inversion Hin. }
    apply elem_of_cons in Hin as [<- | Hin]; simpl.
    { pose proof (esft_edge_sum_mono seen cls entries).
      assert (Hnew : esft_edge_cost (cls :: seen) (cls, Gstruct layout) = 0).
      { unfold esft_edge_cost. simpl. rewrite bool_decide_true; [done | set_solver]. }
      assert (Hold : esft_edge_cost seen (cls, Gstruct layout) = length layout.(s_bases)).
      { unfold esft_edge_cost. simpl. rewrite bool_decide_false; done. }
      rewrite Hnew Hold.
      lia. }
    { specialize (IH Hin). pose proof (esft_edge_cost_mono seen cls entry). lia. }
  Qed.

  Lemma esft_remaining_take seen cls :
    cls ∉ seen ->
    length (esft_children cls) + esft_remaining_edges (cls :: seen) <=
      esft_remaining_edges seen.
  Proof.
    intros Hfresh. unfold esft_children, esft_remaining_edges.
    destruct (glob_def sigma cls) as [decl |] eqn:Hdecl.
    { destruct decl; try apply esft_edge_sum_mono.
      rewrite length_fmap.
      apply esft_edge_sum_take; first exact Hfresh.
      destruct (NM.map_to_list_elements _ _ _ Hdecl) as [before [after Hentries]].
      rewrite Hentries. apply elem_of_app. right. by left. }
    { apply esft_edge_sum_mono. }
  Qed.

  Fixpoint esft_walk (fuel : nat) (seen todo : list name) : bool :=
    match todo with
    | [] => true
    | cls :: todo =>
        match fuel with
        | O => false
        | S fuel =>
            if bool_decide (cls ∈ seen) then esft_walk fuel seen todo
            else esft_node_ok cls &&
              esft_walk fuel (cls :: seen) (esft_children cls ++ todo)
        end
    end.

  Lemma esft_walk_complete fuel seen todo :
    length todo + esft_remaining_edges seen <= fuel ->
    List.Forall esft_class_safe todo -> esft_walk fuel seen todo = true.
  Proof.
    revert seen todo. induction fuel as [| fuel IH]; intros seen todo Hfuel Hsafe;
      destruct todo as [| cls todo]; first done.
    { simpl in Hfuel. lia. }
    { done. }
    simpl. case_bool_decide as Hseen.
    { apply IH; first (simpl in Hfuel; lia).
      inversion Hsafe. assumption. }
    apply andb_true_iff. inversion Hsafe as [| ? ? Hhead Htail]; subst.
    split.
    { exact (esft_safe_node cls Hhead). }
    apply IH.
    { pose proof (esft_remaining_take seen cls Hseen).
      rewrite length_app. simpl in Hfuel. lia. }
    apply Forall_app. split; last exact Htail.
    exact (esft_safe_children cls Hhead).
  Qed.

  Lemma esft_walk_sound fuel seen todo :
    List.Forall (fun cls => esft_node_ok cls = true) seen ->
    (forall cls, cls ∈ seen -> forall base,
      base ∈ esft_children cls -> base ∈ seen ++ todo) ->
    esft_walk fuel seen todo = true ->
    exists visited : list name,
      (forall cls, cls ∈ seen ++ todo -> cls ∈ visited) /\
      List.Forall (fun cls => esft_node_ok cls = true) visited /\
      (forall cls, cls ∈ visited -> forall base,
        base ∈ esft_children cls -> base ∈ visited).
  Proof.
    revert seen todo. induction fuel as [| fuel IH]; intros seen todo Hsafe Hclosed Hrun;
      destruct todo as [| cls todo].
    { exists seen. rewrite app_nil_r in Hclosed. rewrite app_nil_r.
      split; first done. split; assumption. }
    { discriminate Hrun. }
    { exists seen. rewrite app_nil_r in Hclosed. rewrite app_nil_r.
      split; first done. split; assumption. }
    simpl in Hrun. case_bool_decide as Hseen.
    { destruct (IH seen todo Hsafe) as [visited [Hcontains [Hnodes Hedges]]].
      { intros node Hin base Hbase. specialize (Hclosed node Hin base Hbase). set_solver. }
      { exact Hrun. }
      exists visited. split; last (split; assumption).
      intros node Hin. apply Hcontains. set_solver. }
    apply andb_true_iff in Hrun as [Hnode Hrun].
    destruct (IH (cls :: seen) (esft_children cls ++ todo)) as
      [visited [Hcontains [Hnodes Hedges]]].
    { constructor; assumption. }
    { intros node Hin base Hbase. apply elem_of_cons in Hin as [-> | Hin].
      { set_solver. }
      specialize (Hclosed node Hin base Hbase). set_solver. }
    { exact Hrun. }
    exists visited. split; last (split; assumption).
    intros node Hin. apply Hcontains. set_solver.
  Qed.

  Definition shared_ptr_no_esftb (ty : type) : bool :=
    match erase_qualifiers ty with
    | Tnamed cls =>
        match esft_children cls with
        | [] => esft_node_ok cls
        | _ => esft_walk (S (esft_remaining_edges [])) [] [cls]
        end
    | _ => true
    end.

  Lemma shared_ptr_no_esftb_correct ty :
    shared_ptr_no_esftb ty = true <-> shared_ptr_no_esft ty.
  Proof.
    unfold shared_ptr_no_esftb, shared_ptr_no_esft.
    destruct (erase_qualifiers ty) as [] eqn:Hty; try tauto.
    match type of Hty with _ = Tnamed ?name => rename name into cls end.
    destruct (esft_children cls) as [| base bases] eqn:Hchildren.
    { split; last apply esft_safe_node.
      intros Hnode. apply (esft_closed_safe [cls]).
      { constructor; first exact Hnode. constructor. }
      { intros node Hcls child Hchild.
        apply list_elem_of_singleton in Hcls. subst node.
        rewrite Hchildren in Hchild. inversion Hchild. }
      { by left. } }
    split.
    { intros Hrun.
      destruct (esft_walk_sound (S (esft_remaining_edges [])) [] [cls]) as
        [visited [Hcontains [Hnodes Hclosed]]].
      { constructor. }
      { intros node Hcls. inversion Hcls. }
      { exact Hrun. }
      apply (esft_closed_safe visited Hnodes Hclosed).
      apply Hcontains. by left. }
    { intros Hsafe. apply esft_walk_complete.
      { simpl. lia. }
      { constructor; first exact Hsafe. constructor. } }
  Qed.
  Lemma shared_ptr_no_esft_no_bases cls layout :
    glob_def sigma cls = Some (Gstruct layout) -> layout.(s_bases) = [] ->
    (forall pack,
      cls <> Ninst "std::enable_shared_from_this" pack /\
      cls <> Ninst "std::__enable_shared_from_this" pack) ->
    shared_ptr_no_esftb (Tnamed cls) = true.
  Proof.
    intros Hlayout Hbases Hname.
    unfold shared_ptr_no_esftb, esft_children, esft_node_ok.
    cbn [erase_qualifiers]. rewrite Hlayout Hbases. simpl.
    apply esft_name_ok_spec. exact Hname.
  Qed.
End hierarchy.
