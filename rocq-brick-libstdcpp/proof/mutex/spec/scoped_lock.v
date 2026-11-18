Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.specify.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

(* Generic specs for "scoped_lock<T1, T2>". *)
NES.Begin scoped_lock.
  Record M {T : Type} : Type := Mk
  { mutex_ptr : ptr
  ; mutex_q : Qp
  ; mutex_m : T }.
  #[global] Arguments M _ : clear implicits.
  #[global] Arguments Mk {_} _ _ _.
  #[only(lens)] derive M.

  #[global] Hint Opaque mutex_ptr : sl_opacity.

  (* We only write specs in the case of two mutexes in a scoped lock.
    More mutexes is not conceptually more difficult. *)
  Parameter R : forall
      `{Σ : cpp_logic} {σ : genv} ty1 ty2 {T1 T2} mutexR1 mutexR2
      `{!BasicLockable ty1 (T:=T1) mutexR1, !Lockable ty1 mutexR1,
        !BasicLockable ty2 (T:=T2) mutexR2, !Lockable ty2 mutexR2},
      cQp.t -> M T1 * M T2 -> Rep.

  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context (ty1 ty2 : type) {mutexT1 mutexT2 : Type}.
    Context {mutexR1 : cQp.t -> mutexT1 -> Rep} {mutexR2 : cQp.t -> mutexT2 -> Rep}.
    Context `{!BasicLockable ty1 (T:=mutexT1) mutexR1, !Lockable ty1 mutexR1}.
    Context `{!BasicLockable ty2 (T:=mutexT2) mutexR2, !Lockable ty2 mutexR2}.

    #[local] Definition scoped_lock_type :=
      Tnamed ("std::scoped_lock" .<< Apack [Atype ty1; Atype ty2] >>).
    #[only(type_ptr=scoped_lock_type,cfracvalid)] derive R.

    Section with_cfrac.
      Context `{CFrac1 : !CFractional1 mutexR1, CFrac2 : !CFractional1 mutexR2}.
      #[local] Set Default Proof Using "CFrac1 CFrac2".

      #[only(cfractional,ascfractional)] derive R.
    End with_cfrac.

    #[local] Abbreviation R := (R ty1 ty2 mutexR1 mutexR2).

    #[global] Instance R_learn : LearnEqF1 R := ltac:(solve_learnable).

    (* The generated template metadata does not expand parameter packs, so
       register the two-mutex signatures explicitly. *)
    #[local] Abbreviation scoped_lock_name :=
      ("std::scoped_lock" .<< Apack [Atype ty1; Atype ty2] >>) (only parsing).

    Definition ctor_spec : mpred :=
      specify.template.ctor scoped_lock_name [Tref ty1; Tref ty2] $
      \this this
      \arg{mp1} "" (Vptr mp1)
      \pre{q1 m1} mp1 |-> mutexR1 q1$m m1
      \pre{K1} do_lock ty1 mp1 m1 K1
      \arg{mp2} "" (Vptr mp2)
      \pre{q2 m2} mp2 |-> mutexR2 q2$m m2
      \pre{K2} do_lock ty2 mp2 m2 K2
      \post
        this |-> R 1$m (Mk mp1 q1 m1, Mk mp2 q2 m2) ** K1 ** K2.
    #[global] Hint Opaque ctor_spec : sl_opacity.
    #[global] Arguments ctor_spec : simpl never.
    Definition SpecFor_ctor_spec := RegisterSpec ctor_spec.
    #[global] Existing Instance SpecFor_ctor_spec.

    Definition dtor_spec : mpred :=
      specify.template.dtor scoped_lock_name $
      \this this
      \pre{m1 m2} this |-> R 1$m (m1, m2)
      \pre{K1} do_unlock ty1 m1.(mutex_ptr) m1.(mutex_m) K1
      \pre{K2} do_unlock ty2 m2.(mutex_ptr) m2.(mutex_m) K2
      \post K1 ** K2 **
        m1.(mutex_ptr) |-> mutexR1 m1.(mutex_q)$m m1.(mutex_m) **
        m2.(mutex_ptr) |-> mutexR2 m2.(mutex_q)$m m2.(mutex_m).
    #[global] Hint Opaque dtor_spec : sl_opacity.
    #[global] Arguments dtor_spec : simpl never.
    Definition SpecFor_dtor_spec := RegisterSpec dtor_spec.
    #[global] Existing Instance SpecFor_dtor_spec.
  End with_cpp.
NES.End scoped_lock.
