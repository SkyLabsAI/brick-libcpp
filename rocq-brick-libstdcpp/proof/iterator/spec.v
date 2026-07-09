(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.lazy.big_sep.lemmas.
Require Import skylabs.cpp.spec.concepts.

Require Import skylabs.prelude.under_rel_proper.

Require Import skylabs.cpp.slice.
Require Import skylabs.cpp.spec.concepts.

NES.Begin std.
  (** An interface for collection ownership predicates. *)

  Class HasRanges `{Σ : cpp_logic} (ty : type) (C : Set) (V : Type) :=
    { collection_idT := C ;
      dereference : C -> V -> ptr ;
      range (c : collection_idT) (q : cQp.t) (begp : V) (ps : list V) (endp : V) : mpred ;
      (**
         [range iter_ty c q begp ps endp] owns fraction [q] of a collection segment from [begp] (included) to [endp] (excluded).
         [ps] is a list of pointers to the collection elements, and [c] is a collection ID.
         [range] only owns the collection "spine", not the actual payloads.
      *)
      range_frac c : CFractional3 (range c) ;
      (* TODO:
         We omit [CFracValid3 (range c)]: [range] only owns the collection
         spine, and for vectors, this corresponds to no physical ownership.
         Since we typically own [range c q begp ps endp ** ... <other rep with
         fraction q>], we can typically derive [q] is valid anyway. *)
      obs_range_nil c q s0 s1 : Observe [| s0 = s1 |] (range c q s0 [] s1) ;
      obs_range_is_nil c q s ps : Observe [| ps = [] |] (range c q s ps s) ;
      obs_range_cons c q s0 s ss s1 : Observe [| s0 = s |] (range c q s0 (s :: ss) s1) ;
      range_app c q s0 s2 xs ys :
        range c q s0 (xs ++ ys) s2 -|- ∃ s1, range c q s0 xs s1 ∗ range c q s1 ys s2 ;
      obs_range_agree_l c st_end xs : AgreeCF1 (fun q s => range c q s xs st_end) ;
      obs_range_agree_r c st_start xs : AgreeCF1 (fun q s => range c q st_start xs s)
    }.
  #[global] Arguments HasRanges {_ _ _} ty C V : assert.
  #[global] Hint Mode HasRanges - - - + - - : typeclass_instances.
  #[global] Arguments range {_ _ _} ty {C V _} c q begp ps endp : assert.
  #[global] Arguments dereference {_ _ _} ty {C V _} c v : assert.
  #[global] Arguments collection_idT {_ _ _} ty {C V _} : assert.

  #[global] Hint Opaque range : sl_opacity.

  (** * [payload iter_ty coll R ps vs]
      Encapsulates a series objects with [R x] as their [Rep] predicate.

      Provided an instance [HasRanges iter_ty C Iter]m
      - iter_ty : type -- type of an iterator;
      - coll : C       -- identity of source collection;
      - R : A -> Rep   -- specification of individual objects;
      - ps : list Iter -- list of iterator states that can be dereferenced to access individual
                          objects;
      - vs : list A    -- list of values zipped with [ps] to specify each object.
   *)
  sl.lock
  Definition payload `{Σ : cpp_logic,σ : genv} {A}
    (iter_ty : type) `{!HasRanges iter_ty C Iter}
    (coll : C) (R : A -> Rep) (ps : list Iter) (vs : list A) : mpred :=
    [∗ list] p ; v ∈ ps ; vs, dereference iter_ty coll p |-> R v.

(**
   Iterators and ranges
   This file provides abstract predicates to used to specify C++ iterators and ranges.  Iterators
   and ranges are central ideas in the design of the algorithms in the C++ standard library.
   Functions on collections can be made generic by using iterator types or range types.


   # [HasRanges]

   [HasRanges] uses [range] to specify a list of pointers to consecutive elements of a collection
   without specifying what the underlying collection is. A range is delimited by a pair of
   pointers. These endpoints can be taken as the state of a begin / end pair of iterators or as the
   state of a single C++ range object.

   For example, a function that abstractly reverses the values in a range specified by two iterators
   can be specified as follows:
   <<
   Definition reverse_spec {A} (ty iter_ty : type)
       `{!RepFor ty A,                (* [objR] for the objects contained by the range *)
         !RepFor iter_ty (C * It),    (* [objR] for the iterators *)
         !HasRanges iter_ty C It} :=  (* [range] where the endpoints are iterators of type [iter_ty] *)
     \arg{it_begp} "begin" (Vptr it_begp)
     \arg{it_endp} "end"   (Vptr it_endp)
       (* Ownership of `begin` / `end` iterator objects. *)
     \prepost{begp}    it_begp |-> objR iter_ty 1$m begp
     \prepost{endp}    it_endp |-> objR iter_ty 1$m endp
       (* Below, [c] is a collection ID, which is shared between a collection and all ranges taken
          from it.  [ps] is a list of pointers to the objects contained between `[begin,end[`; if
          [ps] is non-empty, the first element is [begp] while [endp] is always excluded.
          IMPORTANT NOTE: [range] does not own any of the elements of the underlying collection.  A
          separate term is provided for that purpose.  *)
     \prepost{c qr ps} range it_ty c qr begp ps endp
     \pre{vs}          payload iter_ty c (objR ty 1$m) ps vs          (* ownership of the elements *)
     \post             payload iter_ty c (objR ty 1$m) ps (reverse vs)
       (* The values of the objects in the range are returned in reversed order.  The list of
          pointers itself is unchanged which guarantees that the reversal is performed in-place. *)
   >>

   In a proof, dereferencing an iterator [itp |-> objR iter_ty q elemp] in the following state:
   <<
     _ : it_begp |-> objR iter_ty 1$m (c, begp)
     _ : it_endp |-> objR iter_ty 1$m (c, endp)
     _ : itp     |-> objR iter_ty 1$m (c, elemp)             <---- dereferencing reads this term
     _ : range iter_ty c qr begp ps0 elemp
     _ : range iter_ty c qr elemp (elemp :: ps1) endp
     _ : [∗ list] p; v ∈ elemp :: ps1; vs,
           dereference iter_ty c p |-> objR ty q v           <---- and gets an object from this term
   >>
   will yield the pointer [dereference iter_ty c elemp] and big sep automation can be used to gain
   access to the corresponding [objR ty] term.

   From that state, incrementing iterator [itp] gets us into the following state:
   <<
     _ : it_begp |-> objR iter_ty 1$m (c, begp)
     _ : it_endp |-> objR iter_ty 1$m (c, endp)
     _ : itp     |-> objR iter_ty 1$m (c, nextp)             <---- these terms changed
     _ : range iter_ty c qr begp (ps0 ++ [elemp]) nextp      <----
     _ : range iter_ty c qr nextp ps1 endp                   <----
     _ : [∗ list] p; v ∈ elemp :: ps1; vs,
           dereference iter_ty c p |-> objR ty q v
   >>


   # [array_spine]

   [array_spine] is the main definition underlying a generic [HasRanges] instance to specify
   iterators and ranges for any array-backed collection.

   It is designed to satisfy the equation:
   <<
        basep |-> array_sliceR ty i j R vs
     -|-
        ∃ ps,
          array_spine ty basep 1$m i ps j **
          [∗ list] idx; v ∈ ps; vs, basep .[ ty ! idx ] |-> R v
   >>
   and thus separate a [array_sliceR] term into a term that specifies a list of pointers and a different
   term to specify the objects that are stored at those pointers.

   NOTE: the listings in this comment are type checked in module [code_snippets].

   # [lookup_result]

   [lookup_result] is a predicate, provided as an automation gadget for specifications that return a
   term of the form [ [| m !! k = Some x |] ]. It helps keep the proposition in the spatial context
   long enough for a hint to turn it into something useful. It is possible that the same can be
   accomplished without [lookup_result].
   More experimentation needed.
 *)
  (**
     [HasRanges]
     Class [HasRanges iter_ty C Iter] defines predicate [range] and related properties for an
     iterator type [iter_ty] or a range type.

       [range iter_ty c q begp ps endp]
                ▲     ▲ ▲  ▲   ▲   ▲
                |     | |  |   |   └--- [ptr], end position of the range (not included);
                |     | |  |   |
                |     | |  |   └------- [list ptr], list of the address of every element of the range;
                |     | |  |
                |     | |  └----------- [ptr], begin position of the range (included);
                |     | |
                |     | └-------------- [cQp.t], fractional ownership;
                |     |
                |     └---------------- [C], contextual information shared by every range taken from
                |                       the same collection;
                |
                └---------------------- [type], iterator type or range type of the object implementing a
                                        range.

     [range] specifies pointers to a series of object without specifying the objects themselves. It
     defines the order of the objects abstractly to allow any collection type to specify its own.  It
     is meant to be easy to split, recombine and move elements between consecutive ranges. Two ranges
     are said to be consecutive iff the end position of one coincides with the beginning position of
     the other.
   *)
  #[local] Open Scope Z_scope.

  Section UPSTREAM.

    Lemma lookup_rangeZ i j (k : nat) x :
      rangeZ i j !! k = Some x <-> i ≤ x < j ∧ x = i + k.
    Proof.
      rewrite -lookupZ_rangeZ lookupZ_Some_to_nat Nat2Z.id.
      intuition; lia.
    Qed.

    #[global] Instance obs_Forall2_big_sepL2 {PROP A B} (R : A -> B -> Prop) (xs : list A) (ys : list B) P :
      (forall k x y, Observe [| R x y |] (P k x y)) ->
      Observe (PROP := PROP) [| Forall2 R xs ys |] (big_sepL2 P xs ys).
    Proof.
      move => HRxy.
      elim/rev_ind: xs ys => [|x xs IH] ys;
        rewrite (big_sepL2_nil_l_inv,big_sepL2_snoc_l_inv).
      - iIntros "-> !> !%"; constructor.
      - iIntros "(%y & %ys' & -> & P & Ps)".
        iDestruct (HRxy with "P") as %?.
        iDestruct (IH with "Ps") as %?.
        iIntros "!> !%".
        apply Forall2_app; repeat first [assumption | constructor].
    Qed.

    Lemma rangeZ_snoc_inv i j x xs : rangeZ i j = xs ++ [x] <-> i < j ∧ j - 1 = x ∧ rangeZ i (j-1) = xs.
    Proof.
      split.
      - case: (Z.lt_ge_cases i j) => Hij.
        + by rewrite rangeZ_snoc // => /app_inj_2 [//|-> [= <-]].
        + by rewrite rangeZ_oob // symmetry_iff app_nil => - [].
      - move => - [Hij [] Hxi Hrng].
        by rewrite rangeZ_snoc // -Hxi Hrng.
    Qed.

  End UPSTREAM.

  Section array.
    #[local] Open Scope Z_scope.
    Context `{Σ : cpp_logic, σ : genv}.
    #[local] Abbreviation IterState := Z (only parsing).

    (**
       [array_spine ty basep q pi xs pj]

       [array_spine] provides a notion of [range] (from [HasRanges]) for any array based
       collection. It allows a conversion between an array-specific definition of a collection to one
       compatible with the notion of iterator specified by [HasRanges].

       In particular, we ensure that the following equivalence holds (lemma
       [array_sliceR_eqv_array_spine_big_sepL2]):
       <<
            basep |-> array_sliceR ty i j R vs
         -|-
            ∃ ps,
              array_spine ty basep 1$m (basep .[ ty ! i]) ps (basep .[ ty ! j]) **
              [∗ list] p; v ∈ ps; vs, p |-> R v
       >>

       so that we can use [basep .[ ty ! i]] and [basep .[ ty ! j]] can be used as the state of an iterator
       in code parameterized by the kind of collection or iterators.

       Limitations:
        1. proving agreement: can't deduce [i = j] from [basep .[ ty ! i] = basep .[ ty ! j]] (lemma is admitted)
        2. CFracValid: [array_spine] has no underlying PCM.
        3. When [array_spine] is given to a function which takes a [range ... begp ps endp]
           precondition and which returns an iterator at index [i] in that range, the state of that
           iterator can be specified abstractly as:
           <<
             ∃ elemp, [| ps !! i = Some elemp |] ** itp |-> objR iter_ty elemp
           >>
           Once returned to the caller and interpretted in that context, the pure term boils down to:
           <<
             [| (fun i => basep .[ ty ! i ] ) <$> rangeZ m n !! i = Some elemp |]
           >>
           Ideally, we should want the automation to see that this entails
           [∃ k, m ≤ k < n ∧ elemp = basep .[ ty ! k ] ] and let us continue our proof from
           there. However, if [ps] is not a fresh variable, substituting it for the [_ <$> rangeZ _ _]
           formulation may not be straightforward.
        4. By using [ptr] as the type for positions, [array_spine] and [HasRanges] cannot specify
           iterations over `vector<bool>`.

       Idea 1:
         include the ownership of the base pointer. It solves 2.
         Issue 1: this does not allow `std::vector` to preserve the validity of iterators after move.
         Issue 2: breaks lemma [array_sliceR_eqv_array_spine_big_sepL2].

       Idea 2:
         To solve 3, [HasRanges] could be reformulated as follows:
         <<
           position : Set ;
           dereference : position -> ptr ;
           range : cQp.t -> position -> list position -> position -> mpred
           (* everything else more or less the same *)
         >>
         and we can instantiate it for [array_spine] as:
         <<
           position := ptr * Z ;
           dereference '(basep, i) := basep .[ ty ! i ] ;
           (* everything else adjusted accordingly *)
         >>
         with this definition, [ps] has all the information we need to find the array subscript
         designated by the resulting iterator.

       Reference from the cppreference page on `std::vector`:
        - after move constructor / assignment, the iterators of `other` remain valid but now reference
          elements of `*this`
     *)
    Definition array_spine (ty : type) (basep : ptr) (q : cQp.t) (i : IterState) (xs : list IterState) (j : IterState) : mpred :=
        [| (i ≤ j)%Z |] ∗
        [| is_Some (size_of σ ty) |]  **
        [| rangeZ i j = xs |]  **
        valid_ptr (basep .[ ty ! j ]) **
        [∗ list] idx ∈ xs, type_ptr ty (basep .[ ty ! idx ]).
    #[global] Arguments array_spine _ _ _ _ !xs _ / : assert.
    #[global] Arguments array_spine : simpl never.
    #[global] Hint Opaque array_spine : sl_opacity.

    Section local_stuff.
      Context {ty : type}.
      Context {basep : ptr}.

      #[local] Abbreviation deref s := ( (basep : ptr) .[ ty ! s ]  ).
      #[local] Abbreviation array_spine := (array_spine ty basep).

      #[global] Instance array_spine_CFractional3 : CFractional3 array_spine.
      Proof.
        rewrite /CFractional/array_spine => *.
        by rewrite -bi.persistent_sep_dup.
      Qed.



      #[global] Instance array_spine_obs_valid_r q s0 ps s1 :
        Observe (valid_ptr (deref s1)) (array_spine q s0 ps s1).
      Proof.
        rewrite /array_spine.
        by iIntros "(%Hij & ? & ? & #A & B) !>".
      Qed.

      #[global] Instance array_spine_obs_valid_l q s0 ps s1 :
        Observe (valid_ptr (deref s0)) (array_spine q s0 ps s1).
      Proof.
        rewrite /array_spine.
        case: ps.
        -
          iIntros "(%Hij & ? & %Hnil & #A & B)".
          move: Hnil => /rangeZ_nil_inv Hji; iIntros "!>".
          by have -> : s0 = s1 by lia.
        - iIntros (p ps) "(%Hij & ? & %Heq & A & #B) !>".
          move: Heq => /rangeZ_cons_inv [? [<- ?]] /=.
          iDestruct "B" as "[B _]".
          iApply (type_ptr_valid with "B").
      Qed.

      #[global] Instance array_spine_obs_has_size q s0 ps s1 :
        Observe [| is_Some (size_of σ ty) |] (array_spine q s0 ps s1).
      Proof. rewrite /array_spine; apply _. Qed.

      Lemma array_spine_unfold q ps i j :
        array_spine q i ps j
          -|-
          [| (i ≤ j)%Z |] ∗
          [| is_Some (size_of σ ty) |]  **
          valid_ptr (basep .[ ty ! j ]) **
          [∗ list] idx; p ∈ rangeZ i j ; ps, [| p = idx |] ∗ type_ptr ty (basep .[ ty ! p ]).
      Proof.
        rewrite /array_spine.
        apply observe_both with (p := is_Some (size_of σ ty)); [> apply _ .. | move => ?].
        apply observe_both with (p := rangeZ i j = ps); [apply _ | | move => Hrng].
        { rewrite big_sepL2_sep.
          iIntros "(%Hij & _ & _ & A & _)".
          rewrite list_eq_Forall2.
          iApply (observe with "A").
          auto using observe_only_provable_impl, obs_Forall2_big_sepL2. }
        f_equiv; rewrite !only_provable_True // !left_id; f_equiv.
        rewrite big_sepL2_rangeZ_l -Hrng; apply big_sepL_proper => k y.
        rewrite lookup_rangeZ => - [_ ->].
        by rewrite only_provable_True // left_id.
      Qed.

      #[global] Instance array_spine_obs_valid q i j k ps (Hbounds : SolveArith (i ≤ j ≤ k)) :
        Observe (valid_ptr (basep .[ ty ! j ])) (array_spine q i ps k).
      Proof.
        case: Hbounds => [] [Hij Hjk].
        have /Zle_lt_or_eq [Hlt|->] : j ≤ k by lia.
        - rewrite array_spine_unfold.
          do 3 apply observe_sep_r.
          have -> : rangeZ i k = rangeZ i j ++ j :: rangeZ (j + 1) k.
          { rewrite -rangeZ_cons // rangeZ_app //. }
          iIntros "A".
          iDestruct (big_sepL2_app_l_inv with "A") as (?? ->) "[_ B]".
          iDestruct (big_sepL2_cons_l_inv with "B") as (?? ->) "[[-> B] _]".
          iApply (observe with "B").
        - apply array_spine_obs_valid_r.
      Qed.

      (* NOTE: it might be simpler to have this equality verbatim in [array_spine] *)
      Lemma array_spine_obs_fmap_rangeZ q ps i j :
        Observe [| ps = rangeZ i j |]
          (array_spine q i ps j).
      Proof.
        rewrite array_spine_unfold.
        rewrite /Observe persistently_only_provable big_sepL2_sep_sepL_r.
        iIntros "(%Hij & _ & _ & A & _)"; iStopProof.
        elim: ps i Hij => [| p ps IH] i Hij; iIntros "A".
        - iDestruct (big_sepL2_nil_r_inv with "A") as %Hji%rangeZ_nil_inv.
          have {Hji Hij} <- : i = j by lia.
          by rewrite rangeZ_nil.
        - iDestruct (big_sepL2_cons_r_inv with "A") as "(%i' & %is' & %Hrng & -> & A)".
          move: Hrng => /rangeZ_cons_inv [{} Hij] [<- {i'}] <- {is'}.
          iDestruct (IH with "A") as "->"; [lia | iPureIntro => {IH}].
          by rewrite [rangeZ i j]rangeZ_cons.
      Qed.

      Lemma array_spine_obs_len q ps i j :
        Observe [| lengthZ ps = j - i |] (array_spine q i ps j).
      Proof.
        rewrite array_spine_unfold.
        iIntros "(%Hij & _ & _ & B)".
        iDestruct (big_sepL2_lengthZ with "B") as %Hlen.
        move: Hlen; rewrite lengthN_rangeZ => <-.
        iIntros "!> !%"; lia.
      Qed.

      #[global] Instance array_spine_obs_nil q s0 s1 :
        Observe [| s0 = s1 |] (array_spine q s0 [] s1).
      Proof.
        iIntros "A".
        iDestruct (array_spine_obs_len with "A") as %Hlen.
        have {Hlen} <- : s0 = s1 by move: Hlen; rewrite lengthN_nil; lia.
        by iIntros "!> !%".
      Qed.

      #[global] Instance array_spine_obs_is_nil q ps s :
        Observe [| ps = [] |] (array_spine q s ps s).
      Proof.
        iIntros "A".
        iDestruct (array_spine_obs_len with "A") as %Hlen.
        iIntros "!> !%".
        apply base.lengthN_nil_inv, (inj Z.of_N).
        by move: Hlen ; rewrite Z.sub_diag.
      Qed.

      #[global] Instance array_spine_obs_cons q s0 s ss s1 :
        Observe [| s0 = s |] (array_spine q s0 (s :: ss) s1).
      Proof.
        rewrite /array_spine => *.
        iIntros "(%Hij & #? & %Hrng & A & B) !> !%".
        by move: Hrng => /rangeZ_cons_inv [?] [<- ?].
      Qed.

      #[global] Instance array_spine_obs_snoc q s0 s ss s1 :
        Observe [| s = s1 - 1 |] (array_spine q s0 (ss ++ [s]) s1).
      Proof.
        rewrite /array_spine => *.
        iIntros "(%Hij & #? & %Hrng & A & B) !> !%".
        by move: Hrng => /rangeZ_snoc_inv [?] [<- ?].
      Qed.

      #[global] Instance array_spine_obs_agree_l st_end xs :
        AgreeCF1 (fun q s => array_spine q s xs st_end).
      Proof.
        iIntros (q1 q2 i i') "A B"; rename st_end into j.
        iDestruct (array_spine_obs_len with "A") as %Hlen0.
        iDestruct (array_spine_obs_len with "B") as %Hlen1.
        have <- : i = i' by lia.
        by iIntros "!> !%".
      Qed.

      #[global] Instance array_spine_obs_agree_r st_start xs :
        AgreeCF1 (fun q s => array_spine q st_start xs s).
      Proof.
        iIntros (q1 q2 j j') "A B"; rename st_start into i.
        iDestruct (array_spine_obs_len with "A") as %Hlen0.
        iDestruct (array_spine_obs_len with "B") as %Hlen1.
        have <- : j = j' by lia.
        by iIntros "!> !%".
      Qed.

      Lemma array_spine_app (q : cQp.t) (s0 s2 : IterState) (xs0 xs1 : list IterState) :
         array_spine q s0 (xs0 ++ xs1) s2 ⊣⊢ ∃ s1 : IterState, array_spine q s0 xs0 s1 ∗ array_spine q s1 xs1 s2.
      Proof.
        rename s0 into i, s2 into k.
        split'.
        - iIntros "A".
          iDestruct (array_spine_obs_len with "A") as %Hlen.
          move: Hlen; rewrite lengthN_app N2Z.inj_add => Hlen.
          iDestruct (observe_elim (valid_ptr (basep .[ ty ! i + lengthZ xs0 ])) with "A") as "[A #?]".
          rewrite array_spine_unfold big_sepL2_app_r_inv.
          iDestruct "A" as (?) "(#Hsize & #Hvalid & %ys0 & %ys1 & %Hys & A & B)".
          iDestruct (big_sepL2_lengthZ with "A") as %Hlen0.
          move: Hys Hlen0 => /rangeZ_app_inv [[]|]; first by lia.
          move => [j] [Hij] [<-] [Hjk <-].
          rewrite lengthN_rangeZ => Hlen0.
          have -> : i + lengthZ xs0 = j by rewrite -Hlen0; lia.
          iExists j.
          by rewrite !array_spine_unfold; iFrame "# ∗".
        - iIntros "(%j & A & B)".
          rewrite !array_spine_unfold big_sepL2_app_r_inv.
          iDestruct "A" as (?) "(Hj & #? & $)".
          iDestruct "B" as (?) "($ & $ & $)".
          iPureIntro; rewrite rangeZ_app //; split; [lia|done].
      Qed.

      Lemma array_spine_rangeZ_split {q i} j {k} (Hij : i ≤ j) (Hjk : j ≤ k) :
        array_spine q i (rangeZ i k) k
          -|-
        array_spine q i (rangeZ i j) j ∗
        array_spine q j (rangeZ j k) k.
      Proof.
        have <- : rangeZ i j ++ rangeZ j k = rangeZ i k
          by rewrite !rangeZ_app //; lia.
        rewrite array_spine_app.
        split'; last iIntros "$".
        iIntros "(%s & A & B)".
        move: (Zle_lt_or_eq _ _ Hij) (Zle_lt_or_eq _ _ Hjk) => {Hij Hjk}
            => - [Hij _|<- [Hjk|<-]].
        - iDestruct (observe_elim [| j - 1 = s - 1 |] with "A") as "[A %Hjs]";
            first by rewrite rangeZ_snoc //; apply _.
          move: Hjs => /Z.sub_cancel_r <-; iFrame.
        - iDestruct (observe_elim [| s = i |] with "B") as "[B ->]";
            first by rewrite rangeZ_cons //; apply _.
          iFrame.
        - rewrite rangeZ_nil.
          iDestruct (observe_elim [| i = s |] with "A") as "[A <-]".
          iFrame.
      Qed.

      Lemma array_sliceR_eqv_array_spine_big_sepL2_rangeZ {A} q i j (R : A -> Rep) (vs : list A) :
        basep |-> array_sliceR ty i j R vs
          -|-
        array_spine q i (rangeZ i j) j **
        [∗ list] p; v ∈ rangeZ i j; vs, deref p |-> R v.
      Proof.
        rewrite array_sliceR.unlock arrayR_eq/arrayR_def arrR_eq/arrR_def.
        rewrite !(_at_sep,_at_only_provable,_at_offsetR,_at_big_sepL,_at_validR).
        split'.
        - iIntros "A".
          rewrite array_spine_unfold.
          iDestruct "A" as "(% & #? & #Hsize & SEP)".
          have ? : i ≤ j by lia.
          have Hi_len : i + length (R <$> vs) = j
            by rewrite length_fmap -lengthZ_correct; lia.
          rewrite o_sub_sub Hi_len.
          iFrame "#".
          rewrite [ [| i ≤ j |] ] only_provable_True // left_id.
          rewrite 2!big_sepL2_rangeZ_l 1!big_opL_fmap.
          rewrite (big_opL_rangeZ vs) //.
          rewrite -big_opL_op.
          iApply (big_sepL_mono with "SEP") => k x Hx.
          rewrite only_provable_True // left_id.
          by rewrite _at_offsetR _at_sep _at_type_ptrR o_sub_sub.
        - iIntros "[A B]".
          iDestruct (array_spine_obs_len with "A") as %Hlen.
          iDestruct (array_spine_obs_has_size with "A") as %Hsize'.
          iDestruct (array_spine_obs_valid_r with "A") as "#valid".
          iDestruct (big_sepL2_lengthZ with "B") as %?.
          have ? : lengthZ vs = j - i by etrans.
          rewrite array_spine_unfold.
          iDestruct "A" as "(%Hij & %Hsize & _ & SEP)".
          rewrite !only_provable_True // !left_id.
          rewrite length_fmap -lengthZ_correct o_sub_sub.
          have -> : i + lengthZ vs = j by lia.
          iFrame "valid".
          rewrite !big_sepL2_rangeZ_l !big_opL_fmap.
          rewrite (big_opL_rangeZ vs) //.
          iCombine "SEP B" as "A".
          rewrite -big_opL_op.
          iApply (big_sepL_mono with "A") => k x Hx.
          rewrite only_provable_True // left_id.
          by rewrite _at_offsetR _at_sep _at_type_ptrR o_sub_sub.
      Qed.

      Lemma array_sliceR_eqv_array_spine_big_sepL2 {A} q i j (R : A -> Rep) (vs : list A) :
             basep |-> array_sliceR ty i j R vs
          -|-
             ∃ ps,
               array_spine q i ps j **
               [∗ list] p; v ∈ ps; vs, deref p |-> R v.
      Proof.
        rewrite (array_sliceR_eqv_array_spine_big_sepL2_rangeZ q).
        split'; first by iIntros "$".
        iIntros "(%ps & A & B)".
        iDestruct (array_spine_obs_fmap_rangeZ with "A") as %->.
        iFrame.
      Qed.

      Lemma array_spine_frac {q} q' begp ps endp :
        array_spine q begp ps endp -|- array_spine q' begp ps endp.
      Proof. by rewrite /array_spine. Qed.

      (* NOTE: This hint loses all [type_ptr] of the [ptr]s in [ps] but they are typically available
         through the array *)
      Lemma array_spine_collect q begp ps endp :
        array_spine q begp ps endp |-- valid_ptr (deref endp).
      Proof.
        iIntros "A".
        iDestruct (array_spine_obs_valid_r with "A") as "#$".
      Qed.

      #[global] Instance learn_array_spine_rangeZ q i ps j :
        Learnable
          emp
          (array_spine q i ps j)
          [ ps = rangeZ i j ].
      Proof. solve_learnable. Qed.

      Definition array_spine_collect_F := [FWD] array_spine_collect.

      Definition congr_array_spine q := normalize.NormCongr4 (fun basep => array_spine basep q).

    End local_stuff.

    #[program]
    Definition array_ranges ty it_ty :
      HasRanges it_ty ptr Z :=
      {| dereference := fun (basep : ptr) st => basep .[ ty ! st ] ;
         range := array_spine ty ;
         range_app basep := array_spine_app ;
      |}.

    Lemma array_sliceR_eqv_spine_payload_rangeZ ty it_ty q (H := array_ranges ty it_ty)
      {A} (basep : ptr) i j (R : A -> Rep) (vs : list A) :
      basep |-> array_sliceR ty i j R vs
        -|-
          array_spine ty basep q i (rangeZ i j) j **
          payload it_ty basep R (rangeZ i j) vs.
    Proof. by rewrite array_sliceR_eqv_array_spine_big_sepL2_rangeZ payload.unlock. Qed.
  End array.

  #[global] Hint Resolve array_spine_collect_F : sl_opacity.
  #[global] Hint Resolve congr_array_spine : tc_strong_opacity.

  Section lookup_result.

    (* gadget meant to facilitate the manipulation of iterators returned from functions. *)
    Definition lookup_result {PROP : bi} {A} (x : option A) (r : A) : PROP :=
      [| x = Some r |].

    #[global] Hint Opaque lookup_result : sl_opacity typeclass_instances.
    #[global] Arguments lookup_result : simpl nomatch.

    Lemma lookup_result_fmap {PROP A B} (f : A -> B) (i : Z) (xs : list A) y :
      lookup_result (PROP := PROP) ((f <$> xs) !! i) y
        |--
        ∃ x (_ : y = f x),
          lookup_result (PROP := PROP) (xs !! i) x.
    Proof.
      rewrite /lookup_result list_lookupZ_fmap.
      iPureIntro => /fmap_Some [x] [-> ->].
      by exists _, eq_refl.
    Qed.

    Definition lookup_result_fmap_F := [FWD] @lookup_result_fmap.

    Lemma lookup_result_rangeZ {PROP} (m n i : Z) x `{Hnorm : !normalize.Normalize eq (i + m)%Z x'} :
      lookup_result (PROP := PROP) (rangeZ m n !! i) x
        |--
        ∃ (_ : x = x'), emp.
    Proof.
      rewrite /lookup_result -{}Hnorm.
      iPureIntro => /lookupZ_rangeZ [? ->].
      by rewrite Z.add_comm; exists eq_refl.
    Qed.

    Definition lookup_result_rangeZ_F := [FWD] @lookup_result_rangeZ.

  End lookup_result.

  #[global] Hint Resolve lookup_result_rangeZ_F : sl_opacity.
  #[global] Hint Resolve lookup_result_fmap_F : sl_opacity.

NES.End std.

(** TODO: update comment to reflect changes to this *)
Module Type CODE_SNIPPETS (U : common.UNIT).
Section code_snippets.
  Context `{Σ : cpp_logic,σ : genv}.
  #[local] Abbreviation WpSpec := (WpSpec mpred val val).
  NES.Open std.

  Definition reverse_spec {A} (ty iter_ty : type)
      `{!BundledRep ty A,                        (* [objR] for the objects contained by the range *)
        !BundledRep iter_ty It,                  (* [objR] for the iterators *)
        !HasRanges iter_ty C It} : WpSpec := (* [range] where the endpoints are iterators of type [iter_ty] *)
    \arg{it_begp} "begin" (Vptr it_begp)
    \arg{it_endp} "end"   (Vptr it_endp)
      (* Ownership of `begin` / `end` iterator objects. *)
    \prepost{begp}    it_begp |-> objR iter_ty 1$m begp
    \prepost{endp}    it_endp |-> objR iter_ty 1$m endp
      (* Below, [c] is a collection ID, which is shared between a collection and all ranges taken
         from it.  [ps] is a list of pointers to the objects contained between `[begin,end[`; if
         [ps] is non-empty, the first element is [begp] while [endp] is always excluded.
         IMPORTANT NOTE: [range] does not own any of the elements of the underlying collection.  A
         separate term is provided for that purpose.  *)
    \prepost{c qr ps} range iter_ty c qr begp ps endp
    \pre{vs}          payload iter_ty c (objR ty 1$m) ps vs    (* ownership of the elements *)
    \post             payload iter_ty c (objR ty 1$m) ps (reverse vs).
      (* The values of the objects in the range are returned in reversed order.  The list of
         pointers itself is unchanged which guarantees that the reversal is performed in-place. *)

  Context {ty iter_ty : type}.
  Context `{!HasRanges iter_ty C Iter}.
  Context `{!BundledRep iter_ty (C * Iter)}.
  Context {it_begp it_endp : ptr}.
  Context {begp endp : Iter}.
  Context {itp : ptr} {elemp : Iter}.
  Context {ps0 ps1 : list Iter}.
  Context {qr q : cQp.t}.
  Context (c : collection_idT iter_ty).
  Context {A} `{!BundledRep ty A} (vs : list A).

  Definition example2 : list mpred :=
    [ it_begp |-> objR iter_ty 1$m (c, begp)
    ; it_endp |-> objR iter_ty 1$m (c, endp)
    ; itp     |-> objR iter_ty 1$m (c, elemp)
    ; range iter_ty c qr begp ps0 elemp
    ; range iter_ty c qr elemp (elemp :: ps1) endp
    ; [∗ list] p; v ∈ (elemp :: ps1); vs, dereference iter_ty c p |-> objR ty q v ]%I.

  Context {nextp : Iter}.

  Definition example3 : list mpred :=
   [ it_begp |-> objR iter_ty 1$m (c, begp)
   ; it_endp |-> objR iter_ty 1$m (c, endp)
   ; itp     |-> objR iter_ty 1$m (c, nextp)
   ; range iter_ty c qr begp (ps0 ++ [elemp]) nextp
   ; range iter_ty c qr nextp ps1 endp
   ; [∗ list] p; v ∈ (elemp :: ps1); vs, dereference iter_ty c p |-> objR ty q v ]%I.

  Context {basep : ptr} (i j : Z) (R : A -> Rep).

  Definition example4 :=
    basep |-> array_sliceR ty i j R vs
      -|-
    ∃ ps,
      array_spine ty basep 1$m i ps j **
      [∗ list] idx; v ∈ ps; vs, basep .[ ty ! idx ] |-> R v.
End code_snippets.
End CODE_SNIPPETS.
