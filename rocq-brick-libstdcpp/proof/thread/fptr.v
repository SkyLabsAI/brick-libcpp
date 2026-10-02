

Require Export skylabs.brick.libstdcpp.thread.prelude.

Require Import skylabs.brick.libstdcpp.mutex.demo_cpp.
Require Import skylabs.brick.libstdcpp.thread.defs.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.prelude.proof.

Locate ht.

Import telescopes .

Definition convert `{Σ : cpp_logic, σ : genv} ty0 ty1 (p0 : ptr) (f : ptr -> mpred) : mpred :=
  let ty2 :=
    match ty1 with
    | Tref ty1 => {%cpp_type "std::reference_wrapper<$ty1>"}
    | _ => ty1
    end in
  let* p1 := fun f =>
    if bool_decide (ty0 = Tref ty2 ∨ ty0 = Trv_ref ty2) then
       (∃ p1, p0 |-> primR (to_heap_type ty0) 1$m (Vptr p1) ∗ f p1)%I
    else if bool_decide (ty0 = tref QM ty2 ∨ ty0 = trv_ref QM ty2) then
       f p0
    else errors.Errors.ERROR ("unsupported conversion: ", (p0, ty0), ty2) in
  match ty1 with
  | Tref ty1 =>
      (∃ p2 : ptr,
         let p1_data := p1 ., {%cpp_name "std::reference_wrapper<$ty1>::_M_data"} in
         (∃ q, p1 |-> std.reference_wrapper.R ty1 q p2) ∗
            (* this is unsound, it's forwarding a
               materialized argument to an inner function *)
         f p1_data )%I
  | _ => f p1
  end.

(** * [precondition_of spec types args k]
    If [spec] has precondition [pre v] and postcondition in two parts [post0 v] and [post1 v p] (p
    is the pointer to the materialized return value) [reified_spec] is equivalent to
    << ∃ v, pre v ** k (post0 v) (post1 v) >>.

    It is meant to be used in the specs of higher order functions so that they can take as a
    precondition the same as that of its function argument and the continuation [k] is given
    the corresponding postcondition which can be used in various ways.
*)
(* mlock *)
Definition precondition_of `{Σ : cpp_logic}
  (S0 : function_spec)
  (targs : list type)
  (args : list ptr) (k : mpred -> (ptr -> mpred) -> mpred) : mpred.
Admitted.
#[global] Hint Opaque precondition_of : sl_opacity.

(* This is the implementation of [precondition_of]. It is built so that we can peel off terms of a
   spec's precondition one by one. *)
Definition partial_precondition `{Σ : cpp_logic}
  (S0 : (ptr -> mpred) -> mpred)
  (k : mpred -> (ptr -> mpred) -> mpred) : mpred.
Admitted.
#[global] Hint Opaque partial_precondition : sl_opacity.

Module precondition_of_hints.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  (*
     Given a list of argument types for a calling function and corresponding argument types for a
     function argument's signature, this attempts to match up the ownership of the resources of one
     set of materialized arguments with that of the other.

     NOTE: This is a bit too specific to the [std::thread::thread] specification.
   *)
  Fixpoint adapt_args (tys0 tys1 : list type) (args : list ptr) (f : list ptr -> mpred) : mpred :=
    match tys0, tys1, args with
    | ty0 :: tys0, ty1 :: tys1, a0 :: args =>
        let* p := convert ty0 ty1 a0 in
        adapt_args tys0 tys1 args (fun ps => f (p :: ps))
    | _, _, _ => f []
    end.

  Lemma precondition_of_unfold S0 decl_targs targs args k :
    force.force list (fs_arguments S0) =[Whd+]=> mret decl_targs ->
    precondition_of S0 targs args k -|-
    let X := fs_spec S0 args in
    let* args' := adapt_args targs decl_targs args in
    partial_precondition (fun k => fs_spec S0 args' k) k.
  Proof. Admitted.
  Definition precondition_of_unfold_B := [BWD->] @precondition_of_unfold.

  Lemma precondition_of_pull_out_sep S0 X Y k :
    (forall Q, S0 Q =[Whd+]=> (X ∗ Y Q)%I) ->
    partial_precondition S0 k -|-
    X ∗ partial_precondition Y k.
  Proof. Admitted.

  Definition precondition_of_pull_out_sep_B := [BWD->] @precondition_of_pull_out_sep.

  Lemma precondition_of_pull_out_exists {T} S0 X k :
    (forall Q, S0 Q =[Whd+]=> (bi_exist (X Q))) ->
    partial_precondition S0 k -|-
    ∃ a : T, partial_precondition (fun Q => X Q a) k.
  Proof. Admitted.
  Definition precondition_of_pull_out_exists_B := [BWD->] @precondition_of_pull_out_exists.

  Lemma precondition_of_pull_wand S0 X Y k :
    (forall Q, S0 Q =[Whd+]=> (X -∗ Y Q)%I) ->
    partial_precondition S0 k -|-
    partial_precondition Y (fun Post0 Post1 => k (X ∗ Post0)%I Post1).
  Proof. Admitted.
  Definition precondition_of_pull_wand_B := [BWD->] @precondition_of_pull_wand.

  Lemma precondition_of_pull_ptr_to_wand S0 X Y k :
    (forall Q, S0 Q =[Whd+]=> (∀ p : ptr, X p -∗ Y Q p)%I) ->
    partial_precondition S0 k -|-
    partial_precondition (fun Q => bi_forall (Y Q))
      (fun Post0 Post1 => k Post0 (fun p => X p ∗ Post1 p)).
  Proof. Admitted.
  Definition precondition_of_pull_ptr_to_wand_B := [BWD->] @precondition_of_pull_ptr_to_wand.

  Lemma precondition_of_intro k :
    partial_precondition (fun Q => bi_forall Q) k -|- k emp (fun p => emp).
  Proof. Admitted.
  Definition precondition_of_intro_B := [BWD->] @precondition_of_intro.

  #[program]
  Definition spec_for_function_ptr_C P cname s
       (_ : find_spec.FindSpec σ true (_global cname) P s) :=
    \cancelx
    \preserving P
    \bound_existential s'
    \instantiate s' := s
    \proving _global cname |-> cptrR s'
    \end.
  Admit Obligations.

End with_cpp.

#[export] Hint Resolve precondition_of_unfold_B : br_hints.
#[export] Hint Resolve precondition_of_pull_out_sep_B : br_hints.
#[export] Hint Resolve precondition_of_pull_out_exists_B : br_hints.
#[export] Hint Resolve precondition_of_pull_wand_B : br_hints.
#[export] Hint Resolve precondition_of_pull_ptr_to_wand_B : br_hints.
#[export] Hint Resolve precondition_of_intro_B : br_hints.

#[export] Hint Resolve spec_for_function_ptr_C : br_hints.

End precondition_of_hints.
