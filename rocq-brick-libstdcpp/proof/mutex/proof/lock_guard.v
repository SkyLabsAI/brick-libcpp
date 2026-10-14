Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock.
Require Import skylabs.brick.libstdcpp.shared_mutex.shared_mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.lock_guard.
Require Import skylabs.brick.libstdcpp.mutex.requirements.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Import lock_guard R_unfold.

(* Verification of the lock_guard template code. *)

#[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.
#[local] Hint Opaque do_lock : sl_opacity.

Definition lock_guard_name (mutex : name) : name :=
  "std::lock_guard" .<< Atype (Tnamed mutex) >>.

(* Pull the C++ lock_guard template AST. *)
Definition lock_guard_ctor_template : Ctor.
Proof.
  let c := eval vm_compute in
    (meta__source.(skylabs.lang.cpp.syntax.templates.msymbols) !!
      (("std::lock_guard" .<< Atype (Tparam "_Mutex") >>) .::
        Nctor [Tref (Tparam "_Mutex")])) in
  lazymatch c with
  | Some (mcore.Template _ (Oconstructor ?ctor)) => exact ctor
  end.
Defined.

Definition lock_guard_ctor_subst (mutex : name) : subst.subst.t :=
  (∅ &: subst.subst._type_param .= {["_Mutex"%pstring := Tnamed mutex]}
     &: subst.subst._resolved_parenlist .=
       {[(Tref (Tnamed mutex), [Tref (Tnamed mutex)]) :=
          fun es => default (Eunsupported "lock_guard reference initializer" Tvoid)
            (head es)]}
     &: subst.subst._resolved_member_type .=
       {[(Tnamed mutex, Nlocal (Nid "lock")) :=
          Tnamed (mutex .:: Nfunction function_qualifiers.N "lock" [])]}
     &: subst.subst._resolved_call .=
       {[(mutex .:: Nfunction function_qualifiers.N "lock" [], []) :=
          fun es => Emember_call false
            (inl (mutex .:: Nfunction function_qualifiers.N "lock" [],
              Direct, "void()"%cpp_type))
            (Emember true (Ethis (Tptr (Tnamed (lock_guard_name mutex))))
              (Nid "_M_device") false (Tref (Tnamed mutex))) es]})%lens.

(* Template lock_guard constructor.  *)
Definition lock_guard_ctor (mutex : name) : Ctor.
Proof.
  let rec extract result :=
    let result := eval cbv -[compare.name_eq_dec compare.type_eq_dec] in result in
    lazymatch result with
    | inr ?ctor => exact ctor
    | context C [compare.name_eq_dec ?n ?n] =>
        let result := context C [@left (n = n) (n ≠ n) eq_refl] in extract result
    | context C [compare.type_eq_dec ?ty ?ty] =>
        let result := context C [@left (ty = ty) (ty ≠ ty) eq_refl] in extract result
    end in
  extract (subst_ap.subst.run2
    (subst_ap.subst.M2.subst_ctor meta__source lock_guard_ctor_template)
    (lock_guard_ctor_subst mutex)).
Defined.

(* Verify that [lock_guard_ctor] specialized to "std::mutex" is equal to the AST
  of "std::lock_guard<std::mutex>::lock_guard(std::mutex&)".
  <lock_guard> can take anything BasicLockable, and we test specializations with
  <mutex>, <recursive_mutex>, <shared_mutex>, and <unique_lock<mutex>>. *)
Lemma lock_guard_ctor_std_mutex_ast :
  source.(symbols) !! "std::lock_guard<std::mutex>::lock_guard(std::mutex&)"%cpp_name =
    Some (Oconstructor (lock_guard_ctor "std::mutex")).
Proof. vm_compute. reflexivity. Qed.

Lemma lock_guard_ctor_std_recursive_mutex_ast :
  source.(symbols) !! "std::lock_guard<std::recursive_mutex>::lock_guard(std::recursive_mutex&)"%cpp_name =
    Some (Oconstructor (lock_guard_ctor "std::recursive_mutex")).
Proof. vm_compute. reflexivity. Qed.

Lemma lock_guard_ctor_std_shared_mutex_ast :
  source.(symbols) !! "std::lock_guard<std::shared_mutex>::lock_guard(std::shared_mutex&)"%cpp_name =
    Some (Oconstructor (lock_guard_ctor "std::shared_mutex")).
Proof. vm_compute. reflexivity. Qed.

Lemma lock_guard_ctor_std_unique_lock_mutex_ast :
  source.(symbols) !! "std::lock_guard<std::unique_lock<std::mutex>>::lock_guard(std::unique_lock<std::mutex>&)"%cpp_name =
    Some (Oconstructor (lock_guard_ctor "std::unique_lock<std::mutex>"%cpp_name)).
Proof. vm_compute. reflexivity. Qed.

Definition lock_guard_struct (mutex : name) (sz al : N) : Struct :=
  Build_Struct []
    [mkMember (Nid "_M_device") (Tref (Tnamed mutex)) false None (Build_LayoutInfo 0)]
    [] [] (lock_guard_name mutex .:: Ndtor) false None Unspecified sz al.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (tu : translation_unit) (mutex : name) (sz al : N).
  Context {mutexT : Type} (mutexR : cQp.t -> mutexT -> Rep).
  Context `{!BasicLockable (Tnamed mutex) mutexR}.

  Definition inner_lock_spec : mpred :=
    specify.exact.method (mutex .:: Nfunction function_qualifiers.N "lock" [])
      function_qualifiers.N Tvoid [] (lock_basic_lockable (Tnamed mutex) mutexR).
  #[local] Hint Opaque inner_lock_spec : sl_opacity.

  Hypothesis Hstruct : tu.(types) !! lock_guard_name mutex =
    Some (Gstruct (lock_guard_struct mutex sz al)).
  (* Assume the specific instantiation of lock_guard for some given mutex code
   exists. *)
  Hypothesis Hcode :
    genv_tu.find_code (lock_guard_name mutex .:: Nctor [Tref (Tnamed mutex)]) tu =
    Some (genv_tu.CTctor (inl (lock_guard_struct mutex sz al)) (lock_guard_ctor mutex)).

  (* Verification of lock_guard.ctor_spec against the template code (Hcode). *)
  Lemma ctor_ok :
    denoteModule tu ** inner_lock_spec |--
    lock_guard.ctor_spec (mutexR:=mutexR) (Tnamed mutex) tu.
  Proof using Hcode Hstruct.
    have Hfuel : exists n, NM.cardinal (tu.(types)) = S n.
    { rewrite NM.cardinal_1.
      have Hin := NM.elements_1 (NM.find_2 Hstruct).
      destruct (NM.elements tu.(types)) eqn:Helems.
      - inversion Hin.
      - eexists. reflexivity. }
    destruct Hfuel as [fuel Hfuel].
    match goal with |- _ |-- ?SP =>
      unshelve epose proof (tactics.VerifySpec.verify_spec_hint_obligation_1
        false false tu σ _ _ Σ _ _
        (genv_tu.CTctor (inl (lock_guard_struct mutex sz al)) (lock_guard_ctor mutex))
        SP ltac:(unfold lock_guard.ctor_spec, specify.template.ctor,
          specify.exact.ctor; apply find_spec.unmaterialized_isspec) ltac:(
          unfold mvcg.find_code_of_type; rewrite Hcode;
          rewrite bool_decide_true; [constructor | reflexivity])) as Hverify
    end.
    iIntros "[#Htu #Hlock]".
    iDestruct (Hverify with "Htu") as "(%Hmodels & Hverify)".
    iApply "Hverify".
    iClear "Hverify".
    clear Hverify.
    unfold lock_guard_ctor, lock_guard_struct, lock_guard_name.
    repeat lazymatch goal with
      | |- environments.envs_entails _ (wp_init_identity _ _ _ _) => fail
      | _ => step
      end.
    PostCondition.hide_post.
    iApply (identity.init_identity_struct' tu (lock_guard_name mutex) _ this Hmodels
      (identity.Rec []) (identity.Rec []) emp emp
      ltac:(cbn zeta; rewrite Hfuel; cbn [identity.derivations];
        rewrite Hstruct; constructor)
      (identity.red_result _) (identity.red_result _)).
    iSplit; first done.
    iIntros "_".
    unfold inner_lock_spec, specify.exact.method, lock_basic_lockable.
    go.
    rewrite wp_minvoke_O.unlock /wp_minvoke /wp_mfptr.
    cbn.
    go.
    iApply (invoke.use_cptrR_method tu _ (Tnamed mutex) CC_C mutex QM
      Tvoid Ar_Definite [] _ _ "void()"%cpp_type mp [] _ eq_refl with "Hlock").
    go.
    iExists (q$m)%cQp, m, K.
    iFrame.
    go.
    by rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
  Qed.
End with_cpp.


(* Specialization of [ctor_ok] for <mutex>, <recursive_mutex>, <shared_mutex>,
  and <unique_lock<mutex>>, whatever that means. *)

Section with_std_mutex.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!mutex.G Σ}.

  Import lock_guard.
  Import R_unfold.

  Lemma ctor_std_mutex_ok :
    denoteModule source ** mutex.lock_spec |--
    lock_guard.ctor_spec "std::mutex" source.
  Proof.
    apply (ctor_ok source "std::mutex" 8 8
      (fun q gP => mutex.R gP.1 q gP.2)).
    - vm_compute. reflexivity.
    - unfold genv_tu.find_code.
      rewrite lock_guard_ctor_std_mutex_ast.
      vm_compute. reflexivity.
  Qed.

  #[global] Instance UNSAFE_R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> learn_eq ==> learn_eq ==> fin_at) mutex.R).
  Proof. solve_learnable. Qed.

  #[local] Instance: `{SplitRecord (M T)} := {}.

  Lemma dtor_ok : verify[source] "std::lock_guard<std::mutex>::~lock_guard()".
  Proof.
    verify_spec.
    rewrite !R.unlock.
    go.
    iExists K, t.
    go with br_erefl.
    by rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
  Qed.

End with_std_mutex.

Section with_std_recursive_mutex.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!std_recursive_mutex.G Σ}.

  Lemma ctor_std_recursive_mutex_ok :
    denoteModule source ** std_recursive_mutex.std_lock_spec_alt |--
    lock_guard.ctor_spec "std::recursive_mutex" source.
  Proof.
    apply (ctor_ok source "std::recursive_mutex" 8 8
      (fun q gP => std_recursive_mutex.R gP.1 q gP.2)).
    - vm_compute. reflexivity.
    - unfold genv_tu.find_code.
      rewrite lock_guard_ctor_std_recursive_mutex_ast.
      vm_compute. reflexivity.
  Qed.
End with_std_recursive_mutex.

Section with_std_shared_mutex.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!shared_mutex.G Σ}.

  Lemma ctor_std_shared_mutex_ok :
    denoteModule source ** shared_mutex.lock_spec |--
    lock_guard.ctor_spec "std::shared_mutex" source.
  Proof.
    apply (ctor_ok source "std::shared_mutex" 8 8
      (fun q gP => shared_mutex.R gP.1 q gP.2)).
    - vm_compute. reflexivity.
    - unfold genv_tu.find_code.
      rewrite lock_guard_ctor_std_shared_mutex_ast.
      vm_compute. reflexivity.
  Qed.
End with_std_shared_mutex.

Section with_std_unique_lock_mutex.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!mutex.G Σ}.

  Definition unique_lock_mutexR (_ : cQp.t) (_ : unit) : Rep :=
    type_ptrR "std::unique_lock<std::mutex>".
  #[local] Hint Opaque unique_lock_mutexR : sl_opacity.

  #[local] Abbreviation unique_lockR :=
    (unique_lock.R "std::mutex" (fun q gP => mutex.R gP.1 q gP.2)).

  Definition unique_lock_mutex_do_lock (this : ptr) (_ : unit) (K : mpred) : mpred :=
    ∃ mm,
      this |-> unique_lockR 1$m (Some mm) **
      [| ~~ mm.(unique_lock.is_held) |] **
      do_lock "std::mutex" mm.(unique_lock.mutex_ptr) mm.(unique_lock.mutex_m)
        (this |-> unique_lockR 1$m
          (Some (mm &: unique_lock._is_held .= true)%lens) -* K).

  Definition unique_lock_mutex_do_unlock (this : ptr) (_ : unit) (K : mpred) : mpred :=
    ∃ mm,
      this |-> unique_lockR 1$m (Some mm) **
      [| mm.(unique_lock.is_held) |] **
      do_unlock "std::mutex" mm.(unique_lock.mutex_ptr) mm.(unique_lock.mutex_m)
        (this |-> unique_lockR 1$m
          (Some (mm &: unique_lock._is_held .= false)%lens) -* K).

  #[local] Instance unique_lock_mutex_basic_lockable :
      BasicLockable "std::unique_lock<std::mutex>" unique_lock_mutexR :=
    {| do_lock := unique_lock_mutex_do_lock;
       do_unlock := unique_lock_mutex_do_unlock |}.

  Lemma unique_lock_mutex_lock_spec :
    unique_lock.lock_spec "std::mutex" source |--
    inner_lock_spec "std::unique_lock<std::mutex>"%cpp_name unique_lock_mutexR.
  Proof.
    unfold unique_lock.lock_spec, inner_lock_spec.
    rewrite specify_notation.template_specify.unlock.
    cbn.
    have -> : resolve_value source "std::unique_lock<std::mutex>"%cpp_name = None
      by vm_compute.
    change (specify.exact.method "std::unique_lock<std::mutex>::lock()"
      function_qualifiers.N Tvoid []
      (\this this
       \pre{mm} this |-> unique_lockR 1$m (Some mm)
       \require ~~ mm.(unique_lock.is_held)
       \pre{K} do_lock "std::mutex" mm.(unique_lock.mutex_ptr)
         mm.(unique_lock.mutex_m) K
       \post this |-> unique_lockR 1$m
         (Some (mm &: unique_lock._is_held .= true)%lens) ** K) |--
      inner_lock_spec "std::unique_lock<std::mutex>"%cpp_name unique_lock_mutexR).
    iApply specify_mono; intros this xs Q.
    unfold lock_basic_lockable, unique_lock_mutex_do_lock.
    cbn.
    ework with br_erefl.
  Qed.

  Lemma ctor_std_unique_lock_mutex_ok :
    denoteModule source ** unique_lock.lock_spec "std::mutex" source |--
    lock_guard.ctor_spec (mutexR := unique_lock_mutexR)
      "std::unique_lock<std::mutex>" source.
  Proof.
    rewrite unique_lock_mutex_lock_spec.
    apply (ctor_ok source "std::unique_lock<std::mutex>"%cpp_name 8 8
      unique_lock_mutexR).
    - vm_compute. reflexivity.
    - unfold genv_tu.find_code.
      rewrite lock_guard_ctor_std_unique_lock_mutex_ast.
      vm_compute. reflexivity.
  Qed.
End with_std_unique_lock_mutex.
