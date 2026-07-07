(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Export skylabs.cpp.slice.

Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.

Require Import skylabs.brick.libstdcpp.vector.inc_vector_cpp.

Require Export skylabs.brick.libstdcpp.allocator.spec.
Require Export skylabs.brick.libstdcpp.iterator.spec.

NES.Begin std.
  #[local] Open Scope Z_scope.

  NES.Begin vector.
    #[global] Abbreviation N ty alloc_ty := (Ninst "std::vector" [Atype ty;Atype alloc_ty]) (only parsing).
    #[global] Abbreviation T ty alloc_ty := (Tnamed (N ty alloc_ty)) (only parsing).

    (**
        NOTE(Simon):
        This state type does not make reference to the state of the allocator or the [max_size] it can
        accommodate.

        TODO: support [max_size] and the allocator state (vector::get_allocator gives direct access to
        it).
     *)
    Record InternalState :=
      { capacity : Z ;
        base_pointer : ptr }.
    #[global] Hint Opaque capacity : sl_opacity.
    #[global] Hint Opaque base_pointer : sl_opacity.

    (**
        Module [std.vector]
        provides a [Rep] predicate for vectors of [ty] using type [alloc_ty] as the allocator. The
        C++ standard library provides <<std::allocator<T> >> as a default choice of allocator and we
        can base a specification on that default using the notations: [std.vector.R],
        [std.vector.R_cap], and [std.vector.R_resized]. [std.vector] provides the [Rep] predicate
        [spineR ty alloc_ty q size st] which specifies the ownership of only the shape of the
        vector, not the payload itself. [size] is the number of elements of the vector whereas
        [st : InternalState] is a record that keeps track of the capacity of the vector and a
        pointer to the memory holding the payloads.

        A vector together with its payload can be specified as:
        <<
           p |-> std.vector.spineR ty alloc_ty q size st **
           base_pointer st |-> array_sliceR ty 0 size Rpayload xs
        >>

        [p |-> std.vector.R ty q xs].
        We can also use the shorthand [p |-> std.vector.R ty q xs] that allows us to omit the type of
        the allocator, the internal state of the vector, its size and the Rep predicate for each
        payload -- using the [RepFor] type class and its projection [objR] as a default for the
        latter.

        The specifications of <<std::vector>> rarely use [std.vector.R] in particular to make it easy to
        prove that memory addresses of the payloads remain constant in certain circumstances.

        Various notations other than [std.vector.R] are provided so that the ownership of a vector can
        be expressed at various levels of abstractions. Because all those shorthands are defined as
        notations, whatever the level of abstraction chosen will result in the use of
        [std.vector.spineR] for the shape of the vector and [array_sliceR] for the payload. Any automation
        that manipulates either will be usable with any use of vectors.

        # Rationale
        The value of leaning heavily on [spineR] and [array_sliceR] the specify the shape of vectors is
        threefold:

         1. We can use basic array automation to reason about random access to elements of a vector as
            well as convenient features such as specifying slices and varying the representation of
            vector elements over time.

         2. We can write specifications for the <<std::vector>> functions with very tight footprints. As
            an example, let us consider a loop, say [for (i = 0; i < v.size(); ++i)], where we iterate
            over the elements of a vector to change their representation from [p .[ ty ! i] |-> RA q x]
            to [p .[ ty ! i] |-> RB q x]. We can specify the loop invariant as
            <<
              basep |-> array_sliceR ty 0 i (RA 1$m) xs0 **
              basep |-> array_sliceR ty i size (RB 1$m) xs1
            >>
            whenever we call [v.size()], only [spineR] is required and there is no need to repackage
            the [array_sliceR] terms into a more homogeneous shape, such as [array_sliceR ty 0 size objR (xs0 ++ xs1)],
            which would be needed by a wider footprint characterization of <<std::vector>>.

         2. The standard makes strong guarantees about the validity of references and iterators within
            a vector and about when storage gets realocated. By focusing our definitions around
            [spineR] and [array_sliceR], we can write strong specifications for the <<std::vector>> functions
            and use the same strong specifications whether the specifications of the client code
            references the internal state of <<std::vector>> or uses more abstract terms to specify
            <<std::vector>> objects.

        To make the comparison more concrete, here are three formulations of the same vector (in
        different states) that can be mixed and matched without complications:

         A) The most abstract, no reference to the internal state:
            <<
              vp |-> std.vector.R ty q (xs0 ++ xs1 ++ xs2)
            >>

         B) Bundled and low-level, concise and allows us to assert that inner references remain valid:
            <<
              vp |-> std.vector.R_cap ty q size st (xs0 ++ xs1 ++ xs2)
            >>

         C) Low-level and detailed, allows us to use our favorite features of [array_sliceR]:
            <<
              vp |-> std.vector.spineR ty alloc_ty q size st **   (* NOTE: should this be called [R_spine] instead? Or
                                                                           [std.vector.internals.R_spine]? *)
              base_pointer st |-> array_sliceR ty 0 i (RA q) xs0 **
              [| xs1 = x :: xs1' |] **
              base_pointer st .[ ty ! i ] |-> RB q x **
              base_pointer st |-> array_sliceR ty (i + 1) j (RC q) xs1' **
              base_pointer st |-> array_sliceR ty j size (RD q) xs2
            >>

        When verifying a piece of code, assertions can alternate between B) and C) when we need
        references to remain valid and we can use A) at points of discontinuity where we no longer use
        the internal references of our vector.

        LIMITATION: this specification applies to the libc++ vectors and does not support
          <<std::vector<bool> >>. To support <<std::vector<bool> >>, we need a different
          construction from [array_sliceR] so that we can track invidividual bits separately.

        LIMITATION: the specification does not discuss exceptions. If allocation fails in
          <<std::vector::reserve>> and callers (i.e. <<std::vector::push_back>>,
          <<std::vector::insert>>, <<std::vector::operator=>>, etc), an exception is thrown.

        NOTE: When printing [spineR] in a goal, because it is a primitive projection, it will be
          printed as [spineR _ _ q x] instead of [spineR ty alloc_ty q x]. Turning on [Printing
          Primitive Projection Parameters] can make this nicer.
     *)
    Parameter spineR :
      forall `{Σ : cpp_logic} {σ : genv} (ty alloc_ty : type)
        (q : cQp.t) (size : Z) (intl : InternalState), Rep.

    sl.lock
    Definition resizedR `{Σ : cpp_logic} (size : Z) (st st' : InternalState) : Rep :=
      if bool_decide (size ≤ capacity st)
      then [| st' = st |]
      else emp.
    #[global] Arguments resizedR {_ _ Σ} size st st' : assert.

    (** Question(Simon): Should we take a predicate as a parameter instead of using [objR]? That would allow varying the
        representation of the contents of the vector of the course of a single proof. That's also enabled by manipulating
        [spineR] and [array_sliceR] separately. *)
    #[global] Notation R_alloc_cap ty alloc_ty q size st xs :=
      ( spineR ty alloc_ty q size st **
        pureR (base_pointer st |-> array_sliceR ty 0 size (objR ty q) xs) )%I
      (q in scope cQp_scope, basep in scope bi_scope, size, cap in scope Z_scope ).

    #[global] Abbreviation R_alloc ty alloc_ty q xs :=
      (∃ size st, R_alloc_cap ty alloc_ty q size st xs )%I
        (q in scope cQp_scope).

    #[global] Abbreviation R_cap ty q size st xs :=
      (R_alloc_cap ty (std.allocator.T ty) q size st xs).

    #[global] Abbreviation R ty q xs :=
      (R_alloc ty (std.allocator.T ty) q xs).

    (** [R_alloc_resized ty alloc_ty q size st xs] is a vector whose payloads can be proven (on
        demand) to be stored in memory specified by [st] if that memory can accommodate [size] elements.
        Otherwise, the memory location of the payloads is unspecified.

        Reference:
          - https://en.cppreference.com/w/cpp/container/vector, section Iterator invalidation
     *)
    #[global] Abbreviation R_alloc_resized ty alloc_ty q size st xs :=
      (∃ st',
         resizedR size st st' **
         R_alloc_cap ty alloc_ty q size st' xs)%I
        (size in scope Z_scope).

      (** See [R_alloc_resized] above *)
    #[global] Abbreviation R_resized ty q size st xs :=
      (R_alloc_resized ty (std.allocator.T ty) q size st xs).

    #[global] Abbreviation null_state := ({| base_pointer := nullptr; capacity := 0 |}).
    (** [R_null q] allows us to specify an empty vector without using a [Rep] predicate for [ty].

        NOTE: Making [nullptr] the unique representation of an empty vector may prevent us from
        proving that iterator [v.begin()] remains valid after we popped the last element of the
        vector *)
    #[global] Abbreviation R_null ty alloc_ty q := (spineR ty alloc_ty q 0 null_state).

    Section spineR_props.
      Context `{Σ : cpp_logic} {σ : genv}.
      Context (ty alloc_ty : type).
      #[local] Abbreviation spineR := (spineR ty alloc_ty).

      #[global] Declare Instance spineR_cfrac : CFractional2 spineR.
      #[global] Declare Instance spineR_ascfrac : AsCFractional2 spineR.
      #[global] Declare Instance spineR_typed q st size :
        Observe (type_ptrR (T ty alloc_ty)) (spineR q size st).
      #[global] Declare Instance spineR_agree q size q' st size' st' :
          Observe2 [| st = st' ∧ size = size' |]
            (spineR q  size  st)
            (spineR q' size' st').
      #[global] Declare Instance spineR_valid_size q size st :
          Observe [| 0 ≤ size ≤ capacity st  |] (spineR q size st).
      #[global] Declare Instance nullptr_valid q size cap :
          Observe [| cap = 0 |] (spineR q size {| base_pointer := nullptr ; capacity := cap |} ).
      #[global] Declare Instance obs_splineR_array_spine q size st :
          Observe (pureR (array_spine ty (base_pointer st) q 0 (rangeZ 0 size) size)) (spineR q size st).
    End spineR_props.

    Module iterator.
      Import skylabs.brick.libstdcpp.iterator.spec.

      #[global] Abbreviation NS := "__gnu_cxx"%cpp_name.
      #[global] Abbreviation N_base const ty alloc_ty :=
        (NS .:: Nid "__normal_iterator" .<< Atype (Tptr (Tconst_if const ty)), Atype (vector.T ty alloc_ty) >> ).
      #[global] Abbreviation T_base const ty alloc_ty := (Tnamed (N_base const ty alloc_ty)).
      sl.lock
      Definition R_base `{Σ : cpp_logic, σ : genv} (const : bool) (ty alloc_ty : type) (q : cQp.t) (basep : ptr) (i : Z) : Rep :=
        _field (N_base const ty alloc_ty .:: Nid "__i_") |-> ptrR<ty> q (basep .[ ty ! i]) **
        structR (N_base const ty alloc_ty) q.
      #[only(type_ptr,ascfractional)] derive R_base.

      #[global] Abbreviation N_alloc ty alloc_ty       := (N_base false ty alloc_ty).
      #[global] Abbreviation N_alloc_const ty alloc_ty := (N_base true ty alloc_ty).
      #[global] Abbreviation T_alloc ty alloc_ty       := (T_base false ty alloc_ty).
      #[global] Abbreviation T_alloc_const ty alloc_ty := (T_base true ty alloc_ty).
      #[global] Abbreviation R_alloc ty alloc_ty       := (R_base false ty alloc_ty).
      #[global] Abbreviation R_alloc_const ty alloc_ty := (R_base true ty alloc_ty).

      #[global] Abbreviation N ty       := (N_base false ty (std.allocator.T ty)).
      #[global] Abbreviation N_const ty := (N_base true ty (std.allocator.T ty)).
      #[global] Abbreviation T ty       := (T_base false ty (std.allocator.T ty)).
      #[global] Abbreviation T_const ty := (T_base true ty (std.allocator.T ty)).
      #[global] Abbreviation R ty       := (R_base false ty (std.allocator.T ty)).
      #[global] Abbreviation R_const ty := (R_base true ty (std.allocator.T ty)).

      Section iter.
        Context `{Σ : cpp_logic, σ : genv}.

        (* TODO: why do we need this instance locally instead of the one we make global? *)
        #[local] Instance iterator_has_rep' is_const ty alloc_ty : concepts.BundledRep (T_base is_const ty alloc_ty) (ptr * Z) :=
          {| objR := fun q st => R_base is_const ty alloc_ty q st.1 st.2 |}.

        (* This has a type similar to [iterator_has_rep'] with some additional variables to
           facilitate unification. *)
        Definition iterator_has_rep is_const ty alloc_ty :=
          make_abstracted_name (T_base is_const ty alloc_ty, Hnf (iterator_has_rep' is_const ty alloc_ty)).

        Definition iter_default_ctor const ty alloc_ty :=
          concepts.default_ctor (T_base const ty alloc_ty) (nullptr, 0).
        #[global] Hint Opaque iter_default_ctor : sl_opacity.
        #[global] Arguments iter_default_ctor : simpl never.
        Definition iter_default_ctor_SpecFor const := RegisterSpec (iter_default_ctor const).
        #[global] Existing Instance iter_default_ctor_SpecFor.

        Definition iter_copy_ctor const ty alloc_ty :=
          concepts.copy_ctor (T_base const ty alloc_ty).
        #[global] Hint Opaque iter_copy_ctor : sl_opacity.
        #[global] Arguments iter_copy_ctor : simpl never.
        Definition iter_copy_ctor_SpecFor const :=
          RegisterSpec (iter_copy_ctor const).
        #[global] Existing Instance iter_copy_ctor_SpecFor.

        Definition iter_dtor const ty alloc_ty := concepts.dtor (T_base const ty alloc_ty).
        #[global] Hint Opaque iter_dtor : sl_opacity.
        #[global] Arguments iter_dtor : simpl never.
        Definition iter_dtor_SpecFor := RegisterSpec (iter_dtor).
        #[global] Existing Instance iter_dtor_SpecFor.

        Definition iter_move_assign const ty alloc_ty :=
          concepts.move_assign (T_base const ty alloc_ty) (fun p => p).
        #[global] Hint Opaque iter_move_assign : sl_opacity.
        #[global] Arguments iter_move_assign : simpl never.
        Definition iter_move_assign_SpecFor :=
          RegisterSpec (iter_move_assign).
        #[global] Existing Instance iter_move_assign_SpecFor.

        Definition iter_deref const ty alloc_ty :=
          let qf := function_qualifiers.mk true false Prvalue in
          specify.template.op (N_base const ty alloc_ty) OOStar qf (Tref (Tconst_if const ty)) [] $
            \this this
            \with basep i
            \let  itemp := basep .[ ty ! i ]
            \prepost{q} this |-> R_base const ty alloc_ty q basep i
            \post[Vref itemp] emp.
        #[global] Hint Opaque iter_deref : sl_opacity.
        #[global] Arguments iter_deref : simpl never.
        Definition iter_deref_SpecFor := RegisterSpec iter_deref.
        #[global] Existing Instance iter_deref_SpecFor.

        Definition iter_op_post_inc const ty alloc_ty :=
          let qf := function_qualifiers.mk false false Prvalue in
          specify.template.op (N_base const ty alloc_ty) OOPlusPlus qf (T_base const ty alloc_ty) [Tint] $
            \this this
            \arg{dummy} "_ignored_" (Vint dummy)
            (* TODO: we need a precondition to state that we don't go out of bounds.
               Maybe something like:
               <<
                 \prepost range (T_base const ty) basep (basep .[ ty ! i ]) [basep .[ ty ! i ]] (basep .[ ty ! i + 1 ])
               >>
               this would have the following benefit:
                - bounds can be checked even when a vector isn't around to specify the bounds
                - available ranges, even if incomplete specify how far we can go with a given iterator
                  even when we don't dereference them
             *)
            \with basep i
            \pre  this |-> R_base const ty alloc_ty 1$m basep i
            \post{prevp}[Vptr prevp]
              prevp |-> R_base const ty alloc_ty 1$m basep i **
              this  |-> R_base const ty alloc_ty 1$m basep (i + 1).
        #[global] Hint Opaque iter_op_post_inc : sl_opacity.
        #[global] Arguments iter_op_post_inc : simpl never.
        Definition iter_op_post_inc_SpecFor := RegisterSpec iter_op_post_inc.
        #[global] Existing Instance iter_op_post_inc_SpecFor.

        Definition iter_op_pre_inc const ty alloc_ty :=
          let qf := function_qualifiers.mk false false Prvalue in
          specify.template.op (N_base const ty alloc_ty) OOPlusPlus qf (Tref (T_base const ty alloc_ty)) [] $
            \this this
            \with basep i
            (* TODO bound-checking, like above *)
            \pre             this |-> R_base const ty alloc_ty 1$m basep i
            \post[Vptr this] this |-> R_base const ty alloc_ty 1$m basep (i + 1).
        #[global] Hint Opaque iter_op_pre_inc : sl_opacity.
        #[global] Arguments iter_op_pre_inc : simpl never.
        Definition iter_op_pre_inc_SpecFor := RegisterSpec iter_op_pre_inc.
        #[global] Existing Instance iter_op_pre_inc_SpecFor.

        Definition iter_op_eq const ty alloc_ty :=
          specify.template.static_op NS OOEqualEqual
              [Atype (Tptr (Tconst_if const ty)); Atype (vector.T ty alloc_ty)]
              Tbool  [Tref (Tconst (T_base const ty alloc_ty)); Tref (Tconst (T_base const ty alloc_ty))] $
            \arg{firstp}  "first"  (Vptr firstp)
            \arg{secondp} "second" (Vptr secondp)
            \with basep i j
            \prepost{q0} firstp  |-> R_base const ty alloc_ty q0 basep i
            \prepost{q1} secondp |-> R_base const ty alloc_ty q1 basep j
            \post[Vbool (bool_decide (i = j))] emp.
        #[global] Hint Opaque iter_op_eq : sl_opacity.
        #[global] Arguments iter_op_eq : simpl never.
        Definition iter_op_eq_SpecFor := RegisterSpec iter_op_eq.
        #[global] Existing Instance iter_op_eq_SpecFor.

        Definition iter_op_ne const ty alloc_ty :=
          specify.template.static_op NS OOExclaimEqual
              [Atype (Tptr (Tconst_if const ty)); Atype (vector.T ty alloc_ty)]
              Tbool  [Tref (Tconst (T_base const ty alloc_ty)); Tref (Tconst (T_base const ty alloc_ty))] $
            \arg{firstp}  "first"  (Vptr firstp)
            \arg{secondp} "second" (Vptr secondp)
            \with basep i j
            \prepost{q0} firstp  |-> R_base const ty alloc_ty q0 basep i
            \prepost{q1} secondp |-> R_base const ty alloc_ty q1 basep j
            \post[Vbool (bool_decide (i <> j))] emp.
        #[global] Hint Opaque iter_op_ne : sl_opacity.
        #[global] Arguments iter_op_ne : simpl never.
        Definition iter_op_ne_SpecFor := RegisterSpec iter_op_ne.
        #[global] Existing Instance iter_op_ne_SpecFor.

        Definition specs const ty alloc_ty :=
          iter_default_ctor const ty alloc_ty **
          iter_copy_ctor const ty alloc_ty **
          iter_dtor const ty alloc_ty **
          iter_move_assign const ty alloc_ty **
          iter_deref const ty alloc_ty **
          iter_op_post_inc const ty alloc_ty **
          iter_op_pre_inc const ty alloc_ty **
          iter_op_eq const ty alloc_ty **
          iter_op_ne const ty alloc_ty.

      End iter.
      #[global] Existing Instance iterator_has_rep.

      Section hints.
        Context `{Σ : cpp_logic, σ : genv}.

        #[global] Instance R_base_learn c ty alloc_ty : LearnEqF2 (R_base c ty alloc_ty) := ltac:(solve_learnable).

        Definition congr_iterator_R_base := normalize.NormCongr4 iterator.R_base.
      End hints.
      #[global] Hint Resolve congr_iterator_R_base : tc_strong_opacity.

    End iterator.

    #[global] Abbreviation range_base const ty alloc_ty := (std.range (iterator.T_base const ty alloc_ty)).
    #[global] Abbreviation range ty alloc_ty            := (std.range (iterator.T_alloc ty alloc_ty)).
    #[global] Abbreviation range_const ty alloc_ty      := (std.range (iterator.T_alloc_const ty alloc_ty)).

    #[global] Abbreviation payload_base const ty alloc_ty := (std.payload (iterator.T_base const ty alloc_ty)).
    #[global] Abbreviation payload ty alloc_ty            := (std.payload (iterator.T_alloc ty alloc_ty)).
    #[global] Abbreviation payload_const ty alloc_ty      := (std.payload (iterator.T_alloc_const ty alloc_ty)).

    Section with_cpp.
      Context `{Σ : cpp_logic, σ : genv}.
      Context (ty alloc_ty : type).

      NES.Open allocator_traits.

      #[local] Abbreviation vector := (N ty alloc_ty) (only parsing).	(** [vector<ty, alloc_ty>] *)
      #[local] Abbreviation vectorT := (Tnamed vector) (only parsing).

      #[local] Abbreviation R_null q := (spineR ty alloc_ty q 0 null_state).
      #[local] Abbreviation R q xs := (R_alloc ty alloc_ty q xs).
      #[local] Abbreviation R_cap q size st xs := (R_alloc_cap ty alloc_ty q size st xs).

      (** See [R_resized] and [R_alloc_resized] above *)
      #[local] Abbreviation R_resized q size s xs := (R_alloc_resized ty alloc_ty q size s xs).

      #[local] Abbreviation spineR q size st := (spineR ty alloc_ty q size st).
      #[local] Abbreviation size_type := (allocator_traits.size_type alloc_ty).

      Definition default_ctor :=
        specify.template.ctor vector [] $
          \this this
          \post this |-> R_null (cQp.m 1).
      #[global] Hint Opaque default_ctor : sl_opacity.
      #[global] Arguments default_ctor : simpl never.
      Definition SpecFor_default_ctor := RegisterSpec default_ctor.
      #[global] Existing Instance SpecFor_default_ctor.

      Definition ctor_with_alloc `{!BundledRep alloc_ty AllocT} :=
        specify.template.ctor vector [alloc_ty] $
          \this this
          \arg{allocp} "alloc" (Vptr allocp)
          \prepost{a} allocp |-> objR alloc_ty (cQp.m 1) a
          \post this |-> R_null (cQp.m 1).
      #[global] Hint Opaque ctor_with_alloc : sl_opacity.
      #[global] Arguments ctor_with_alloc : simpl never.
      Definition SpecFor_ctor_with_alloc := RegisterSpec default_ctor.
      #[global] Existing Instance SpecFor_ctor_with_alloc.

      Section allocator.
        Context `{!IsAllocator alloc_ty}.
        Context `{!BundledRep ty V}.

        Section default_ctor.
          Context `{!DefaultValue ty V}.

          Definition sized_ctor :=
            specify.template.ctor vector [size_type; alloc_ty] $
              \this this
              \arg{size} "size" (Vint size)
              \arg{allocp} "alloc" (Vptr allocp)
              \prepost{a} allocp |-> objR alloc_ty (cQp.m 1) a
              \post this |-> R (cQp.m 1) (replicateZ size (default_val ty)).
          #[global] Hint Opaque sized_ctor : sl_opacity.
          #[global] Arguments sized_ctor : simpl never.
          Definition SpecFor_sized_ctor := RegisterSpec sized_ctor.
          #[global] Existing Instance SpecFor_sized_ctor.
        End default_ctor.

        Definition init_ctor :=
          specify.template.ctor vector [size_type; Tref (Tconst ty); alloc_ty] $
            \this this
            \arg{size} "size" (Vint size)
            \arg{vp}   "v0"   (Vref vp)
            \arg{allocp} "alloc" (Vptr allocp)
            \prepost{v0 vq} vp |-> objR ty vq v0
            \prepost{a}  allocp |-> objR alloc_ty (cQp.m 1) a
            \post this |-> R (cQp.m 1) (replicateZ size v0).
        #[global] Hint Opaque init_ctor : sl_opacity.
        #[global] Arguments init_ctor : simpl never.
        Definition SpecFor_init_ctor := RegisterSpec init_ctor.
        #[global] Existing Instance SpecFor_init_ctor.

        Definition copy_alloc_ctor :=
          specify.template.ctor vector [Tref (Tconst vectorT); Tref (Tconst alloc_ty)] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \arg{allocp} "alloc" (Vptr allocp)
            \prepost{q__other size st xs}
                  otherp |-> R_cap q__other size st xs
            \prepost{a}  allocp |-> objR alloc_ty (cQp.m 1) a
            \post this |-> R (cQp.m 1) xs.
        #[global] Hint Opaque copy_alloc_ctor : sl_opacity.
        #[global] Arguments copy_alloc_ctor : simpl never.
        Definition SpecFor_copy_alloc_ctor := RegisterSpec copy_alloc_ctor.
        #[global] Existing Instance SpecFor_copy_alloc_ctor.

        Definition move_alloc_ctor :=
          specify.template.ctor vector [Trv_ref vectorT; Tref (Tconst alloc_ty)] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \arg{allocp} "alloc" (Vptr allocp)
            \pre{size st xs}
                   otherp |-> R_cap  (cQp.m 1) size st xs
            \post* otherp |-> R_null (cQp.m 1)
            \prepost{a}  allocp |-> objR alloc_ty (cQp.m 1) a
            \post this |-> R_cap (cQp.m 1) size st xs.
        #[global] Hint Opaque move_alloc_ctor : sl_opacity.
        #[global] Arguments move_alloc_ctor : simpl never.
        Definition SpecFor_move_alloc_ctor := RegisterSpec move_alloc_ctor.
        #[global] Existing Instance SpecFor_move_alloc_ctor.

      End allocator.

      Section no_alloc.
        Context `{!BundledRep ty V}.

        Definition copy_ctor :=
          specify.template.ctor vector [Tref (Tconst vectorT)] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \prepost{q__other size st xs}
                  otherp |-> R_cap q__other size st xs
            \let cap := capacity st
            \post
              Exists new_basep,
                 let new_st := {| base_pointer := new_basep; capacity := cap |} in
                 this |-> R_cap (cQp.m 1) size new_st xs.
        #[global] Hint Opaque copy_ctor : sl_opacity.
        #[global] Arguments copy_ctor : simpl never.
        Definition SpecFor_copy_ctor := RegisterSpec copy_ctor.
        #[global] Existing Instance SpecFor_copy_ctor.

        Definition move_ctor :=
          specify.template.ctor vector [Trv_ref vectorT] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \pre{size st xs}
                   otherp |-> R_cap (cQp.m 1) size st xs
            \post* otherp |-> R_null  (cQp.m 1)
            \post this |-> R_cap (cQp.m 1) size st xs.
        #[global] Hint Opaque move_ctor : sl_opacity.
        #[global] Arguments move_ctor : simpl never.
        Definition SpecFor_move_ctor := RegisterSpec move_ctor.
        #[global] Existing Instance SpecFor_move_ctor.

        Definition dtor :=
          specify.template.dtor vector $
            \this this
            \pre{xs} this |-> R (cQp.m 1) xs
            \post emp .
        #[global] Hint Opaque dtor : sl_opacity.
        #[global] Arguments dtor : simpl never.
        Definition SpecFor_dtor := RegisterSpec dtor.
        #[global] Existing Instance SpecFor_dtor.

        Definition subscript `{!IsAllocator alloc_ty} c :=
          let qf := function_qualifiers.mk c false Prvalue in
          specify.template.op vector OOSubscript qf (Tref (Tconst_if c ty)) [size_type] $
            \this this
            \arg{i} "i" (Vint i)
            \prepost{q size st} this |-> spineR q size st
            \require 0 ≤ i < size (** This is probably required in order to have `type_ptr` on the resulting reference *)
            \post[Vref (base_pointer st .[ ty ! i])] emp .
        #[global] Hint Opaque subscript : sl_opacity.
        #[global] Arguments subscript : simpl never.
        Definition SpecFor_subscript := RegisterSpec (@subscript).
        #[global] Existing Instance SpecFor_subscript.

        Definition push_back_copy :=
          let qf := function_qualifiers.N in
          specify.template.method vector "push_back" qf Tvoid [Tref (Tconst ty)] $
            \this this
            \arg{p} "p" (Vref p)
            \prepost{q x} p |-> objR ty q x
            \pre{size st xs}
                      this |-> R_cap (cQp.m 1) size st xs
            \post     this |-> R_resized (cQp.m 1) (size + 1) st (xs ++ [x]).
        #[global] Hint Opaque push_back_copy : sl_opacity.
        #[global] Arguments push_back_copy : simpl never.
        Definition SpecFor_push_back_copy := RegisterSpec push_back_copy.
        #[global] Existing Instance SpecFor_push_back_copy.

        Definition push_back_move `{!concepts.MovedValue ty V} :=
            let qf := function_qualifiers.N in
            specify.template.method vector "push_back" qf Tvoid [Trv_ref ty] $
            (* specify.template.ctor vector "push_back" qf [Trv_ref ty] $ *)
              \this this
              \arg{p} "p" (Vref p)
              \pre{x}   p |-> objR ty (cQp.m 1) x
              \post*    p |-> moved_objR ty (cQp.m 1) x
              \pre{size st xs}
                        this |-> R_cap (cQp.m 1) size st xs
              \post     this |-> R_resized (cQp.m 1) (size+1) st (xs ++ [x]).
        #[global] Hint Opaque push_back_move : sl_opacity.
        #[global] Arguments push_back_move : simpl never.
        Definition SpecFor_push_back_move := RegisterSpec (@push_back_move).
        #[global] Existing Instance SpecFor_push_back_move.

        Definition pop_back :=
            let qf := function_qualifiers.N in
            specify.template.method vector "pop_back" qf Tvoid [] $
              \this this
              \with size st xs x
              \pre  this |-> R_cap (cQp.m 1) size st (xs ++ [x])
              \post this |-> R_resized (cQp.m 1) (size - 1) st xs.
        #[global] Hint Opaque pop_back : sl_opacity.
        #[global] Arguments pop_back : simpl never.
        Definition SpecFor_pop_back := RegisterSpec pop_back.
        #[global] Existing Instance SpecFor_pop_back.

        Definition back c :=
            let qf := function_qualifiers.mk c false Prvalue in
            specify.template.method vector "back" qf (Tref (Tconst_if c ty)) [] $
              \this this
              \with q size st
              \require 0 < size
              \prepost this |-> spineR q size st
              \let backp := base_pointer st .[ ty ! size - 1 ]
              \post[Vptr backp] emp.
        #[global] Hint Opaque back : sl_opacity.
        #[global] Arguments back : simpl never.
        Definition SpecFor_back := RegisterSpec back.
        #[global] Existing Instance SpecFor_back.

        Definition front c :=
            let qf := function_qualifiers.mk c false Prvalue in
            specify.template.method vector "front" qf (Tref (Tconst_if c ty)) [] $
              \this this
              \with q size st
              \require 0 < size
              \prepost this |-> spineR q size st
              \let backp := base_pointer st .[ ty ! 0 ]
              \post[Vptr backp] emp.
        #[global] Hint Opaque front : sl_opacity.
        #[global] Arguments front : simpl never.
        Definition SpecFor_front := RegisterSpec front.
        #[global] Existing Instance SpecFor_front.

        Definition clear :=
          let qf := function_qualifiers.N in
          specify.template.method vector "clear" qf Tvoid [] $
            \this this
            \with size st xs
            \pre  this |-> R_cap (cQp.m 1) size st xs
            \post this |-> R_cap (cQp.m 1) 0 st [].
        #[global] Hint Opaque clear : sl_opacity.
        #[global] Arguments clear : simpl never.
        Definition SpecFor_clear := RegisterSpec clear.
        #[global] Existing Instance SpecFor_clear.

        Definition resize_default `{!concepts.DefaultValue ty V,!IsAllocator alloc_ty} :=
          let qf := function_qualifiers.N in
          specify.template.method vector "resize" qf Tvoid [size_type] $
            \this this
            \arg{new_size} "new_size" (Vint new_size)
            \with size st xs
            \pre  this |-> R_cap (cQp.m 1) size st xs
            \post
              ∃ xs',
                (if bool_decide (size = new_size) then
                   [| xs' = xs |]
                 else if bool_decide (new_size < size) then     (* it would be better to have [new_size ≤
                                                                   size] for when neither [new_size = size]
                                                                   nor [new_size ≠ size] *)
                   [| xs' = takeN (Z.to_N new_size) xs |]       (* would [sliceZ] be better here (because of Z vs N)? *)
                 else (* size < new_size *)
                   [| xs' = xs ++ replicateZ (new_size - size) (default_val ty) |] ) ∗
                this |-> R_resized (cQp.m 1) new_size st xs'.
        #[global] Hint Opaque resize_default : sl_opacity.
        #[global] Arguments resize_default : simpl never.
        Definition SpecFor_resize_default := RegisterSpec (@resize_default).
        #[global] Existing Instance SpecFor_resize_default.

        Definition resize `{!IsAllocator alloc_ty} :=
          let qf := function_qualifiers.N in
          specify.template.method vector "resize" qf Tvoid [size_type; Tref (Tconst ty)] $
            \this this
            \arg{new_size} "new_size" (Vint new_size)
            \arg{vp}       "v0"       (Vptr vp)
            \prepost{q v0} vp |-> objR ty q v0
            \with size st xs
            \pre  this |-> R_cap (cQp.m 1) size st xs
            \post
              ∃ xs',
                (if bool_decide (size = new_size) then
                   [| xs' = xs |]
                 else if bool_decide (new_size < size) then     (* it would be better to have [new_size ≤
                                                                   size] for when neither [new_size = size]
                                                                   nor [new_size ≠ size] *)
                   [| xs' = takeN (Z.to_N new_size) xs |]       (* would [sliceZ] be better here (because of Z vs N)? *)
                 else (* size < new_size *)
                   [| xs' = xs ++ replicateZ (new_size - size) v0 |] ) ∗
                this |-> R_resized (cQp.m 1) new_size st xs'.
        #[global] Hint Opaque resize : sl_opacity.
        #[global] Arguments resize : simpl never.
        Definition SpecFor_resize := RegisterSpec (@resize).
        #[global] Existing Instance SpecFor_resize.

        Definition size `{!IsAllocator alloc_ty} :=
          let qf := function_qualifiers.Nc in
          specify.template.method vector "size" qf size_type [] $
            \this this
            \with q size st
            \prepost this |-> spineR q size st
            \post[Vint size] emp.
        #[global] Hint Opaque size : sl_opacity.
        #[global] Arguments size : simpl never.
        Definition SpecFor_size := RegisterSpec (@size).
        #[global] Existing Instance SpecFor_size.

      End no_alloc.
      Section iterators.

        Definition begin_spec const :=
          let qf := function_qualifiers.mk const false Prvalue in
          specify.template.method vector "begin" qf (iterator.T_base const ty alloc_ty) [] $
            \this this
            \prepost{q size st}
                  this |-> spineR q size st
            \post{itp}[Vptr itp] itp |-> iterator.R_base const ty alloc_ty 1$m (base_pointer st) 0.
        #[global] Hint Opaque begin_spec : sl_opacity.
        #[global] Arguments begin_spec : simpl never.
        Definition SpecFor_begin_spec := RegisterSpec begin_spec.
        #[global] Existing Instance SpecFor_begin_spec.

        Definition end_spec const :=
          let qf := function_qualifiers.mk const false Prvalue in
          specify.template.method vector "end" qf (iterator.T_base const ty alloc_ty) [] $
            \this this
            \prepost{q size st}
                  this |-> spineR q size st
            \post{itp}[Vptr itp] itp |-> iterator.R_base const ty alloc_ty 1$m (base_pointer st) size.
        #[global] Hint Opaque end_spec : sl_opacity.
        #[global] Arguments end_spec : simpl never.
        Definition SpecFor_end_spec := RegisterSpec end_spec.
        #[global] Existing Instance SpecFor_end_spec.

        (**
           [vector_has_ranges] should have type [HasRanges (iterator.T_base const ty)].
           Type class search then wouldn't find it so we use the notation [make_abstracted_name]
           defined in [cpp/spec/specify.v]

           [vector_has_ranges] is defined as specialization of the generic array [HasRanges]
           instance.

           TODO: this needs to be less abstruse. *)
        Definition vector_has_ranges const :=
             make_abstracted_name (* this notation rewrites type [it_ty] to make it easier to match
                                     modulo [const] *)
               ( let it_ty := iterator.T_base const ty alloc_ty in
                 (it_ty, std.array_ranges ty it_ty)).
        #[global] Existing Instance vector_has_ranges.

      End iterators.

      Section specs.
        Context `{!IsAllocator alloc_ty}.
        Context `{!BundledRep ty V}.
        Context `{!DefaultValue ty V}.
        Context `{!MovedValue ty V}.

        #[local] Abbreviation MaybeConst spec := (spec true ** spec false).

        Definition specs :=
          default_ctor **
          ctor_with_alloc **
          sized_ctor **
          init_ctor **
          copy_alloc_ctor **
          move_alloc_ctor **
          copy_ctor **
          move_ctor **
          dtor **
          MaybeConst subscript **
          push_back_copy **
          push_back_move **
          pop_back **
          MaybeConst front  **
          MaybeConst back **
          clear **
          resize_default **
          resize **
          size **
          MaybeConst begin_spec **
          MaybeConst end_spec.

      End specs.

    End with_cpp.

    Section instances_hints.
      Context `{Σ : cpp_logic} {σ : genv} (ty alloc_ty : type).

      #[global] Instance nullptr_cap_size q size cap :
        Observe ([| cap = 0 |] ** [| size = 0 |])
          (spineR ty alloc_ty q size {| base_pointer := nullptr ; capacity := cap |}).
      Proof.
        iIntros "H".
        iDestruct (observe_elim_pure (0 ≤ size ≤ cap) with "H") as %Hsize.
        { apply spineR_valid_size. }
        iDestruct (nullptr_valid with "H") as %->.
        move: Hsize => /= /ZMicromega.eq_le_iff <-.
        by iIntros "!>".
      Qed.
      Definition nullptr_cap_size_F := ltac:(mk_obs_fwd nullptr_cap_size).

      #[global] Instance learn_spineR :
        LearnEqF2 (spineR ty alloc_ty) := ltac:(solve_learnable).

      #[global] Instance learn_array_spine (p : ptr) q q' st ps size i j :
        Learnable
          (p |-> vector.spineR ty alloc_ty q size st)
          (std.array_spine ty  (vector.base_pointer st) q' i ps j
          )
          [q = q' ].
      Proof. solve_learnable. Qed.

      #[global] Instance resizedR_affine size s s' : Affine (resizedR size s s').
      Proof. rewrite resizedR.unlock; apply _. Qed.

      Lemma trivial_resized_elim (p basep : ptr) size s' :
        p |-> resizedR size {| base_pointer := basep ; capacity := 0 |} s' |-- emp.
      Proof. rewrite resizedR.unlock; by iIntros. Qed.
      Definition trivial_resized_elim_F := [FWD] trivial_resized_elim.

      #[program]
      Definition vector_spine_intro_CB (p : ptr) q q' st size i j :=
        \cancelx
        \preserving p |-> spineR ty alloc_ty q size st
        \let basep := vector.base_pointer st
        \proving std.array_spine ty  basep q' i (rangeZ i j) j
        \bound A (R : A -> Rep)
        \proving{(vs : list A)} payload ty alloc_ty basep R (rangeZ i j) vs
        \through basep |-> array_sliceR ty i j R vs
        \end.
      Next Obligation.
        intros. iIntros "$" (???) "A".
        iDestruct (array_sliceR_eqv_spine_payload_rangeZ with "A") as "[$ $]".
      Qed.

      #[program]
      Definition vector_spine_elim_CF (p : ptr) q st size i j (Harith : SolveArith (0 ≤ i ≤ j ≤ size)) :=
        \cancelx
        \preserving p |-> spineR ty alloc_ty q size st
        \let basep := vector.base_pointer st
        \with A (R : A -> Rep)
        \using{(vs : list A)} payload ty alloc_ty basep R (rangeZ i j) vs
        \deduce basep |-> array_sliceR ty i j R vs
        \end.
      Next Obligation.
        intros; case: Harith => [[] Hi0 [] Hij Hj_size].
        iIntros "(A & B)".
        iDestruct (observe_elim (array_spine _ _ _ _ _ _) with "A") as "[$ C]".
        { apply observe_intuitionistically_if, _at_observe_pureR, _. }
        have ? : 0 ≤ j by lia.
        rewrite (array_spine_rangeZ_split j) // (array_spine_rangeZ_split i) //.
        iDestruct "C" as "([_ C] & _)".
        rewrite array_sliceR_eqv_spine_payload_rangeZ.
        iFrame "B C".
      Qed.

      Definition congr_spineR q := normalize.NormCongr2 (vector.spineR ty alloc_ty q).
      Definition congr_resizedR s s' := normalize.NormCongr1 (fun size => vector.resizedR size s s').

    End instances_hints.
    #[global] Hint Resolve nullptr_cap_size_F learn_spineR trivial_resized_elim_F : sl_opacity.

    #[global] Hint Resolve vector_spine_elim_CF : sl_opacity.
    #[global] Hint Resolve vector_spine_intro_CB : sl_opacity.

    #[global] Hint Resolve congr_spineR : tc_strong_opacity.
    #[global] Hint Resolve congr_resizedR : tc_strong_opacity.

  NES.End vector.

NES.End std.
