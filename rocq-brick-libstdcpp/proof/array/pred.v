(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.array.spec.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.const.

(** * Laws for [std.array]

    The specifications in [std.array] state ownership as [std.array.R]. This file
    connects [std.array.R] to the shapes in which ownership of a <<std::array>>
    reaches a proof by other routes:

    - const transport: [wp_make_const]/[wp_make_mutable] at a <<const std::array>>
      local or field;
    - element-wise ownership: value or aggregate initialization yields
      [array_sliceR ty i j (primR ty q) vs] over [val]s, while [std.array.R] is over
      the element model;
    - <<cpp.class … dataclass>>: a <<std::array>> field gets [std.array.fieldR],
      which unfolds to [std.array.R], as its representation (end of this file). *)

NES.Begin std.array.
  #[local] Open Scope Z_scope.

  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.

    (** Needed, with the [cfractional] instances derived in [std.array], for
        [std.array.R] to be a field of a dataclass ([CFracSplittable]). *)
    #[global] Instance spineR_timeless ty n q : Timeless (spineR ty n q).
    Proof. rewrite spineR.unlock. apply _. Qed.

    (** ** Const transport

        [wp_const] at <<std::array<ty, n> >> descends into the class layout of the
        translation unit it is evaluated in. The laws below read that layout from
        that translation unit, so, unlike a [const.CONST] law stated at this
        library's translation unit, they need no [type_table_le] side condition and
        apply in every client.

        [prim_const_ok ty] holds for unqualified value types: those whose [wp_const]
        transports a single [primR]. *)
    Definition prim_const_ok (ty : type) : bool :=
      is_value_type ty &&
      negb (qual_norm (fun cv _ => q_const cv) ty) &&
      bool_decide (erase_qualifiers ty = ty).

    (** [wp_const] at the array type <<ty[sz]>>, element by element. *)
    Lemma array_sliceR_wp_const_fold tu ty {A} (f : A -> val) (sz : BinNums.N) from to (p : ptr) xs Q :
      prim_const_ok ty = true ->
      p |-> array_sliceR ty 0 (Z.of_N sz) (fun x => primR ty from (f x)) xs
      |-- (p |-> array_sliceR ty 0 (Z.of_N sz) (fun x => primR ty to (f x)) xs -* Q) -*
          fold_left (fun Q i => wp_const tu from to (p .[ ty ! Z.of_N i ]) ty Q) (seqN 0 sz) Q.
    Proof.
      rewrite /prim_const_ok => /andb_prop [/andb_prop [Hval /(proj1 (negb_true_iff _)) Hq] /bool_decide_eq_true_1 Hty].
      induction sz as [|sz IH] using N.peano_ind in xs, Q |- *.
      - rewrite seqN_0 /= array_sliceR_eq_bounds.
        iIntros "H HQ". iApply "HQ". by rewrite array_sliceR_eq_bounds.
      - rewrite seqN_S_end_app fold_left_app N2Z.inj_succ N.add_0_l /=.
        rewrite (array_sliceR_snoc_inv (fun x => primR ty from (f x))); last lia.
        have -> : Z.succ (Z.of_N sz) - 1 = Z.of_N sz by lia.
        rewrite !(_at_exists, _at_sep, _at_only_provable, _at_offsetR).
        iIntros "(%x & %xs' & -> & Rx & Tx & A) HQ".
        rewrite -(primR_wp_const_val _ _ _ _ _ _ (Is_true_eq_left _ Hval)) Hq Hty.
        iExists (f x). iFrame "Rx". iIntros "Rx".
        iApply (IH xs' Q with "A"). iIntros "A".
        iApply "HQ".
        rewrite array_sliceR_snoc.
        have -> : Z.succ (Z.of_N sz) - 1 = Z.of_N sz by lia.
        rewrite -_at_type_ptrR. iFrame.
    Qed.

    Lemma array_sliceR_wp_const tu ty {A} (f : A -> val) (sz : BinNums.N) (n : Z) from to (p : ptr) xs Q :
      Z.of_N sz =[Vm?]= n ->
      prim_const_ok ty =[Vm?]=> true ->
      p |-> array_sliceR ty 0 n (fun x => primR ty from (f x)) xs
      |-- (p |-> array_sliceR ty 0 n (fun x => primR ty to (f x)) xs -* Q) -*
          wp_const tu from to p (Tarray ty sz) Q.
    Proof.
      move=> /RedEq_eq <- /RedEq_eq Hok.
      have Hty : erase_qualifiers ty = ty.
      { by move: Hok => /andb_prop [_ /bool_decide_eq_true_1]. }
      rewrite -wp_const_intro.
      cbn [decompose_type qual_norm qual_norm' q_const].
      rewrite Hty.
      iIntros "A B". iApply fupd_intro.
      iApply (array_sliceR_wp_const_fold with "A [B]"); first done.
      iIntros "A". iApply fupd_intro. by iApply "B".
    Qed.
    Definition array_sliceR_wp_const_C := [CANCEL] array_sliceR_wp_const.

    (** ** The const-transport law

        [R_wp_const] is the const-transport law for [std.array.R]: for every
        translation unit [tu] in which <<std::array<ty, n> >> has libstdc++'s layout
        ([struct_ok]), and every element representation that is a [primR] of [ty]
        (which covers [objR ty] for the arithmetic, character, <<bool>> and pointer
        types).

        It is [const.CONST1] except that [tu] is the translation unit [wp_const] is
        evaluated in, rather than one related to it by [type_table_le], and that it
        holds at every pair of fractions. Stated at this library's translation unit,
        a [const.CONST] law would not apply in clients: <<string/pred.v>> and
        <<libgtest>> record that [type_table_le] between a library and a client unit
        is false in practice, because the two elaborate different libstdc++
        template internals. *)
    Definition struct_ok (ty : type) (n : Z) (st : Struct) : bool :=
      bool_decide (0 < n) && prim_const_ok ty && negb (has_vtable st) &&
      match st.(s_bases), st.(s_fields) with
      | [], [m] =>
          bool_decide (m.(mem_name) = field_name.Id "_M_elems") &&
          bool_decide (m.(mem_type) = Tarray ty (Z.to_N n)) &&
          negb m.(mem_mutable)
      | _, _ => false
      end.

    Lemma R_wp_const tu ty n st {A} (f : A -> val) from to (p : ptr) xs Q :
      tu.(types) !! N ty n = Some (Gstruct st) ->
      struct_ok ty n st = true ->
      p |-> R_gen ty n from (fun x => primR ty from (f x)) xs
      |-- (p |-> R_gen ty n to (fun x => primR ty to (f x)) xs -* Q) -*
          wp_const tu from to p (T ty n) Q.
    Proof.
      move=> Hst /andb_prop [/andb_prop [/andb_prop [/bool_decide_eq_true_1 Hn Hok] /(proj1 (negb_true_iff _)) Hvt] Hl].
      move: Hl. case Hb : (s_bases _) => [|??] //. case Hf : (s_fields _) => [|m [|??]] //.
      move=> /andb_prop [/andb_prop [/bool_decide_eq_true_1 Hm /bool_decide_eq_true_1 Hmt] /(proj1 (negb_true_iff _)) Hmm].
      rewrite -wp_const_intro.
      cbn [decompose_type qual_norm qual_norm' q_const].
      rewrite Hst Hb Hf /= Hmt Hm Hmm Hvt.
      rewrite spineR.unlock !_at_sep _at_only_provable _at_offsetR.
      iIntros "[[S %] A] HQ". iApply fupd_intro.
      (* NOTE: pass the [=[Vm?]=] premises explicitly: left to typeclass search
         with the extent still an evar, they do not terminate. *)
      have E1 : Z.of_N (Z.to_N n) =[Vm?]= n by apply RedEq_if_eq; rewrite Z2N.id; lia.
      have E2 : prim_const_ok ty =[Vm?]=> true by apply RedEq_if_eq.
      iApply (array_sliceR_wp_const _ _ _ _ _ _ _ _ _ _ E1 E2 with "A [S HQ]").
      iIntros "A". iFrame "S". iIntros "S". iApply fupd_intro. iApply "HQ".
      rewrite _at_offsetR. iFrame "S A". iPureIntro; lia.
    Qed.

    (** The law as a backward hint, for integer elements. Backward rather than
        cancellation: by the time a <<const>> local is made mutable again its
        ownership is typically split (the spine into fractions, the elements into
        cells), and proving the reassembled [std.array.R] is the automation's job.
        The layout is looked up the same way BRiCk's [wp_const_named_struct] does. *)
    Lemma R_wp_const_Vint tu ty n st from to (p : ptr) Q :
      tu.(types) !! N ty n =[Vm?]=> Some (Gstruct st) ->
      struct_ok ty n st =[Vm?]=> true ->
      (Exists xs : list Z,
        p |-> R_gen ty n from (fun x => primR ty from (Vint x)) xs **
        (p |-> R_gen ty n to (fun x => primR ty to (Vint x)) xs -* Q))
      |-- wp_const tu from to p (T ty n) Q.
    Proof.
      move=> /RedEq_eq Hst /RedEq_eq Hok.
      iIntros "(%xs & R & HQ)". by iApply (R_wp_const with "R HQ").
    Qed.
    Definition R_wp_const_Vint_B := [BWD] R_wp_const_Vint.

    (** ** Element-wise ownership

        Value or aggregate initialization of a <<std::array>> of integers leaves
        [array_sliceR ty i j (primR ty q) vs] for a list [vs] of [Vint]s, while
        [std.array.R] (with [objR ty q] reduced) wants
        [array_sliceR ty i j (fun x => primR ty q (Vint x)) xs]. [ints_of_vals] reads
        [xs] back from [vs]. *)
    Definition ints_of_vals (vs : list val) : option (list Z) :=
      mapM (fun v => match v with Vint z => Some z | _ => None end) vs.

    Lemma ints_of_vals_Some vs xs : ints_of_vals vs = Some xs -> vs = Vint <$> xs.
    Proof.
      rewrite /ints_of_vals.
      elim: vs xs => [|v vs IH] xs /=; first by move=> [<-].
      case: v => // z. case E : (mapM _ vs) => [ys|] //= [<-].
      by rewrite (IH _ E).
    Qed.

    (** The fold/unfold law, as an equivalence. *)
    Lemma array_sliceR_Vint ty i j q (xs : list Z) :
      array_sliceR ty i j (primR ty q) (Vint <$> xs) -|-
      array_sliceR ty i j (fun x => primR ty q (Vint x)) xs.
    Proof. apply array_sliceR_fmap. Qed.

    (** The fold direction as a forward hint: a [val]-indexed slice of [Vint]s is
        normalized to the model-indexed one as soon as it appears. A cancellation
        hint would not do: the specifications quantify the contents
        (<<\pre{xs} this |-> R 1$m xs>>), and the automation does not pick the
        witness of such an existential through a cancellation hint. *)
    Lemma array_sliceR_fold_Vint ty i j q (vs : list val) (xs : list Z) (p : ptr) :
      ints_of_vals vs =[Vm?]=> Some xs ->
      p |-> array_sliceR ty i j (primR ty q) vs
      |-- p |-> array_sliceR ty i j (fun x => primR ty q (Vint x)) xs.
    Proof. move=> /RedEq_eq /ints_of_vals_Some ->. by rewrite array_sliceR_Vint. Qed.
    Definition array_sliceR_fold_Vint_F := [FWD] array_sliceR_fold_Vint.
  End with_cpp.

  #[global] Hint Resolve array_sliceR_wp_const_C R_wp_const_Vint_B : sl_opacity.
  #[global] Hint Resolve array_sliceR_fold_Vint_F : sl_opacity.

  (** [fieldR ty n Relem q xs] is [R_gen ty n q (Relem q) xs]: the representation
      dataclass synthesis gives a <<std::array<ty, n> >> field, [Relem] being the
      synthesized representation of [ty]. It is a transparent definition so that it
      unfolds to [std.array.R] by conversion; dataclass synthesis treats it as an
      atom, which matters because its lazy-unfolding pass fails ("Bound variable …
      not found") on the nested offsets and element lambda of the unfolded form. *)
  Definition fieldR `{Σ : cpp_logic} {σ : genv} (ty : type) (n : Z) {A}
      (Relem : cQp.t -> A -> Rep) (q : cQp.t) (xs : list A) : Rep :=
    R_gen ty n q (Relem q) xs.
  #[global] Hint Opaque fieldR : sl_opacity.

  Lemma fieldR_unfold `{Σ : cpp_logic} {σ : genv} ty n {A} (Relem : cQp.t -> A -> Rep) q xs (p : ptr) :
    p |-> fieldR ty n Relem q xs -|- p |-> R_gen ty n q (Relem q) xs.
  Proof. done. Qed.
  Definition fieldR_unfold_F `{Σ : cpp_logic} {σ : genv} := [FWD->] fieldR_unfold.
  Definition fieldR_unfold_B `{Σ : cpp_logic} {σ : genv} := [BWD->] fieldR_unfold.
  #[global] Hint Resolve fieldR_unfold_F fieldR_unfold_B : sl_opacity.

  (** The class template, as it appears in [Ninst]. *)
  Definition template_name : name := Nscoped (Nglobal (Nid "std")) (Nid "array").

NES.End std.array.

(** ** <<std::array>> fields in <<cpp.class … dataclass>>

    Dataclass synthesis knows the model and representation of a field type only if
    it is builtin or registered for that exact name (<<cpp.model>>/<<cpp.rep>>, keyed
    by translation unit). These two rules teach it every <<std::array<ty, n> >>
    whose element type it knows, mirroring its own rules for <<ty[n]>>: the model is
    [list M] for the element model [M], and the representation is
    [std.array.fieldR ty n Relem] for the element representation [Relem], which
    unfolds to [std.array.R_gen ty n q (Relem q)]. For the builtin element types
    that is exactly [std.array.R ty n q] with [objR ty q] reduced, as it appears
    once a specification is in context. *)
Elpi Accumulate skylabs.synth.db lp:{{
  namespace std.array {
    % [Ty] is <<std::array<ETy, Len> >> (up to unfolding the name).
    pred match-type i:term, o:term, o:term.
    match-type {{ Tnamed lp:GN }} ETy Len :-
      coq.reduction.lazy.norm GN GN',
      GN' = {{ Ninst lp:Base [Atype lp:ETy; Avalue (Eint lp:Len _)] }},
      coq.reduction.lazy.norm {{ std.array.template_name }} Base.

    pred beta-apps i:term, i:list term, o:term.
    beta-apps (fun _ _ B) [A|As] R :- !, beta-apps (B A) As R.
    beta-apps T [] T.
  }

  synth.model.of_type.loop CTy M :- std.array.match-type CTy ETy _, !, std.do! [
    synth.model.to_term {synth.model.of_type.loop ETy} EM,
    synth.model.of_type.inferred CTy {{ list lp:EM }} M,
  ].

  synth.rep.of_type.loop CTy M RF :- std.array.match-type CTy ETy Len, !, std.do! [
    synth.rep.of_type.loop ETy EM ERF,
    synth.model.to_term EM EMT,
    synth.rep.rfunc.to_term EM ERF ET,
    T0 = {{ fun (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) (σ : genv) (q : cQp.t) (xs : list lp:EMT) =>
             @std.array.fieldR ti _Σ Σ σ lp:ETy lp:Len lp:EMT (lp:ET ti _Σ Σ σ) q xs }},
    coq.eval_lazy coq.redflags.beta T0 T,
    (pi ti\ pi Sigma\ pi cl\ pi g\ pi q\ pi l\
      std.array.beta-apps T [ti, Sigma, cl, g, q, l] (R ti Sigma cl g q l)),
    synth.rep.of_type.inferred CTy {{ list lp:EMT }} R M RF,
  ].
}}.
