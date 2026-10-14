Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp_templates.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

(* Generic specs for "lock_guard<T>". *)
NES.Begin lock_guard.
  Record M {T : Type} : Type := Mk
  { mutex_ptr : ptr
  ; mutex_q : Qp
  ; mutex_m : T }.
  #[global] Arguments M _ : clear implicits.
  #[global] Arguments Mk {_} _ _ _.
  #[only(lens)] derive M.

  #[global] Hint Opaque mutex_ptr : sl_opacity.

  (* Wrapper of a basic lockable object with resource predicate [mutexR]. *)
  sl.lock
  Definition R
      `{Σ : cpp_logic} {σ : genv} ty {T} mutexR `{!BasicLockable ty (T:=T) mutexR}
      (q : cQp.t) (m : M T) : Rep :=
    let lgty := "std::lock_guard" .<< Atype ty >> in
    structR lgty q **
    _field (lgty .:: Nid "_M_device") |-> refR<ty> q m.(mutex_ptr) **
    pureR (m.(mutex_ptr) |-> mutexR (cQp.scale m.(mutex_q) q) m.(mutex_m)).

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    #[global] Instance repfor `{Σ : cpp_logic} {σ : genv} ty {T} mutexR `{!BasicLockable ty (T:=T) mutexR} :
      rep.RepFor.C (Tnamed $ "std::lock_guard" .<< Atype ty >>)
        [ArgType.CFrac; ArgType.Constant _] (R ty mutexR) := {}.
  End with_RepFor.

  Module R_unfold.
    #[only(lazy_unfold(export))] derive R.
  End R_unfold.

  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context ty {mutexT mutexR} `{!BasicLockable ty (T:=mutexT) mutexR}.

    #[only(type_ptr)] derive R.
    #[only(cfracvalid)] derive R.

    Section with_cfrac.
      Context `{CFrac : !CFractional1 mutexR}.
      #[local] Set Default Proof Using "CFrac".

      #[global] Instance R_cfrac : CFractional1 (R ty mutexR).
      Proof. rewrite R.unlock. apply _. Qed.

      #[global] Instance R_as_cfrac : AsCFractional1 (R ty mutexR).
      Proof. solve_as_cfrac. Qed.

      Lemma mutex_borrow mp m (this : ptr) (q1 q2 : Qp) :
        this |-> R ty mutexR 1$m (Mk mp (q1 + q2) m) |--
        mp |-> mutexR q1$m m **
        this |-> R ty mutexR 1$m (Mk mp q2 m).
      Proof.
        rewrite R.unlock /= !cQp.scale_mut !(right_id_L 1%Qp Qp.mul).
        change ((q1 + q2)$m)%cQp with (q1$m + q2$m)%cQp.
        rewrite (cfractional (P := λ q, mutexR q m)).
        iIntros "($ & $ & $ & $)".
      Qed.
    End with_cfrac.

    #[local] Abbreviation R := (R ty (T:=mutexT) mutexR).

    #[global] Instance R_learn : LearnEqF1 R := ltac:(solve_learnable).

    (* Register the instantiated signature directly so it can also be verified
       with a symbolic mutex type. Keep [tu] for the existing spec interface. *)
    Definition ctor_spec (tu : translation_unit) : mpred :=
      specify.template.ctor ("std::lock_guard" .<< Atype ty >>) [Tref ty] $
      \this this
      \arg{mp} "" (Vptr mp)
      \pre{q m} mp |-> mutexR q$m m
      \pre{K} do_lock ty mp m K
      \post
        this |-> R 1$m (Mk mp q m) ** K.
    #[global] Hint Opaque ctor_spec : sl_opacity.
    #[global] Arguments ctor_spec : simpl never.
    Definition SpecFor_ctor_spec := RegisterSpec (ctor_spec source).
    #[global] Existing Instance SpecFor_ctor_spec.

    cpp.spec "std::lock_guard<$ty>::~lock_guard()" as dtor_spec from source templates templates (
      \\with
      \this this
      \pre{m} this |-> R 1$m m
      \pre{K} do_unlock ty m.(mutex_ptr) m.(mutex_m) K
      \post K ** m.(mutex_ptr) |-> mutexR m.(mutex_q)$m m.(mutex_m)
    ).
  End with_cpp.
NES.End lock_guard.
