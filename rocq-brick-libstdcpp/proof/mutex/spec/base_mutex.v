Require Import iris.algebra.gset.
Require Import iris.algebra.lib.excl_auth.

Require Import skylabs.bi.tls_modalities.
Require Import skylabs.bi.tls_modalities_rep.
Require Import skylabs.bi.weakly_objective.
Require Import skylabs.auto.cpp.weakly_local_with.

Require Import skylabs.auto.cpp.spec.
Require Import skylabs.auto.cpp.proof.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Export lock_ghost2.mutex_set_G (mutex_set_G).

Import linearity.

(** A BASE_MUTEX_PREDS module says a mutex spec is parametrized by some
  `token` and `locked`. The exact model depends on the implementation.

  These predicates do not depend on the calling convention: they are shared by
  the C++ mutex specs in [skylabs.brick.libstdcpp.mutex.spec.mutex] and the
  pthread mutex specs in [skylabs.brick.libstdcpp.pthread.mutex]. There,
  CPP_MUTEX_PREDS adds the BasicLockable and Lockable named requirements of C++
  mutex types. *)

Module Type BASE_MUTEX_PREDS.
  Parameter gname : Set.
  Parameter cpp_ty : type.
  Parameter mutex_inv_namespace : gname -> namespace.
  (* The invariant namespace cannot be [nroot] for practical purposes.
   TODO maybe other mutex preds should also have this? *)
  Axiom mutex_inv_namespace_not_root : forall g, mutex_inv_namespace g <> nroot.

  Parameter G : forall `{Σ : cpp_logic}, Type.
  Existing Class G.
  #[global] Arguments G {_ _} Σ : assert.

  (** [cQp.t] describes the permissions transferred by lock and unlock.
      The permission might involve points-to, so use cQp.t instead of QP. *)
  Parameter token : forall `{Σ : cpp_logic, !G Σ},
    gname -> cQp.t -> mpred.
  Definition not_locked `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv}
      (this : ptr) (g : gname) (th : thread_idT) (qt : cQp.t) : mpred :=
    token g qt ** MutexSets.my_mutexes th
      (coPset.CoPset $ ↑mutex_inv_namespace g).
  #[global] Hint Opaque not_locked : sl_opacity typeclass_instances.

  Parameter locked : forall `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv},
    ptr -> gname -> thread_idT -> cQp.t -> mpred.

  #[global] Declare Instance token_fractional
      `{Σ : cpp_logic, !G Σ} γ : CFractional (token γ).
  #[global] Declare Instance token_timeless
      `{Σ : cpp_logic, !G Σ} γ q : Timeless (token γ q).
  #[global] Instance not_locked_timeless
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ th q :
    Timeless (not_locked this γ th q).
  Proof. rewrite /not_locked. apply _. Qed.
  (** Each thread has at most one handle to attempt locking this mutex. *)
  #[global] Instance not_locked_exclusive
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ th :
    Exclusive1 (not_locked this γ th).
  Proof.
    intros q1 q2. rewrite /not_locked.
    iIntros "[_ H1] [_ H2]".
    have Hoverlap : ~ ((↑mutex_inv_namespace γ : coPset) ## ↑mutex_inv_namespace γ).
    { have Hnonempty := nclose_non_empty (mutex_inv_namespace γ). set_solver. }
    iDestruct (MutexSets.my_mutexes_exclusive th
      (↑mutex_inv_namespace γ) (↑mutex_inv_namespace γ) Hoverlap
      with "[$H1 $H2]") as %[].
  Qed.
  #[global] Declare Instance locked_timeless
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ th q :
    Timeless (locked this γ th q).
  #[global] Declare Instance locked_exclusive
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ :
    Exclusive2 (locked this γ).

  #[global] Declare Instance locked_WeaklyObjective
      `{Σ : cpp_logic, MUTEX_SETS : !mutex_set_G Σ, !G Σ} {σ : genv} this γ th q :
    WeaklyObjective (locked this γ th q).

  Section with_cpp.
    Context `{Σ : cpp_logic}.

    (** Fractional ownership of a mutex guarding the predicate <<P>>. *)
    Parameter R : forall `{MUTEX_SETS : !mutex_set_G Σ, !G Σ}
      {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> mpred -> Rep.
    Context `{MUTEX_SETS : !mutex_set_G Σ}.
    Context `{!G Σ}.
    #[global] Hint Opaque R : sl_opacity typeclass_instances.
    #[only(cfractional,cfracvalid,ascfractional)] derive R.
    #[global] Declare Instance R_type_ptr : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv} g q P,
      Observe (type_ptrR cpp_ty) (R g q P).
    #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
        Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

    Context {σ : genv}.
    Context {HAS_THREADS : HasStdThreads Σ}.

    #[global] Instance locked_learn :
        Cbn (Learn (req_eq ==> learn_eq ==> req_eq ==> req_eq ==> learn_hints.fin) locked).
    Proof. solve_learnable. Qed.

    (** Can switch the protected resource from [emp] to [P].
        FIXME maybe it should be any [P'] to [P]?
        
        Initializing [this |-> R old 1$m emp] probably depends on the mutex
        implementation. *)
    Axiom init_R : forall (this : ptr) (old : gname)
        (N : namespace) (P : mpred),
      WeaklyObjective P -> 
      N <> nroot ->
      this |-> R old 1$m emp ** token old 1$m ** ▷P |--
        (|={⊤}=> ∃ g,
          [| mutex_inv_namespace g = N |] **
          this |-> R g 1$m P ** token g 1$m).

    (** For any [h1],[h2] ∈ {[locked _ _ th _], [not_locked _ _ th _]}, we
      would like [h1 ** h2 ⊢ False] because there should be at most one such
      handle for thread [th]. We already have [locked_exclusive] and
      [not_locked_exclusive], so we also want [locked ** not_locked ⊢ False].
      But here we require something more specific because it is easier for the
      implementation proof: we don't need the whole [not_locked] but just the
      [my_mutex] part, and we also need to prove this by opening the mutex
      invariant in [R], thus the [this |-> R ...] in the LHS and the update on
      the RHS. *)
    Axiom locked_my_mutexes_exclusive : forall (this : ptr) g th q qt P E,
      ↑mutex_inv_namespace g ⊆ E ->
      this |-> R g q P ** locked this g th qt **
        MutexSets.my_mutexes th
          (coPset.CoPset $ ↑mutex_inv_namespace g) |-- (|={E}=> False).

  End with_cpp.
End BASE_MUTEX_PREDS.

(* TODO UPSTREAM. FIXME what does this do? *)
#[global] Instance SplitRecord_prod A B : SplitRecord (@prod A B) := {}.

(** Contracts shared by every mutex over [BASE_MUTEX_PREDS], whatever its
    calling convention. *)
Module base_mutex_spec (Preds : BASE_MUTEX_PREDS).
Section with_cpp.
  Import Preds.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!G Σ}.
  Context {HAS_THREADS : HasStdThreads Σ}.


  (** Choose a sibling namespace for an auxiliary invariant. *)
  Lemma mutex_inv_namespace_disjoint g :
    ∃ No : namespace, mutex_inv_namespace g ## No.
  Proof.
    have HN := mutex_inv_namespace_not_root g.
    destruct (mutex_inv_namespace g) as [[|p ns]]; first done.
    exists (Namespace ns .@ Pos.succ p).
    have -> : Namespace (p :: ns) = Namespace ns .@ p.
    { by rewrite namespaces.ndot_unseal. }
    apply ndot_ne_disjoint. lia.
  Qed.

  Lemma locked_not_locked_exclusive (this : ptr) g th q qt qt' P E :
    ↑mutex_inv_namespace g ⊆ E ->
    this |-> R g q P ** locked this g th qt ** not_locked this g th qt' |--
      (|={E}=> False).
  Proof.
    rewrite /not_locked. iIntros (Hmask) "(HR & HL & _ & Hnames)".
    iApply (locked_my_mutexes_exclusive with "[$HR $HL $Hnames]"). done.
  Qed.

  (** * Contract bodies

      Each body describes the mutex [this] without binding it, and returns
      [ret]: C++ member functions bind [this] with [\this] and return [void] or
      [bool], while the pthread functions take it as an argument and return an
      [int] status. Unfold a body with [Reduce] when registering a spec. *)

  (** The guarded predicate must be weakly objective for invariant allocation,
      which R likely has. *)
  Definition ctor_body (ret : val) (this : ptr) : WpSpec mpred val val :=
    (\pre{N P} ▷P
     \require N <> nroot
     \require WeaklyObjective P
     \post[ret] |={⊤}=> Exists g,
       [| mutex_inv_namespace g = N |] **
       this |-> R g 1$m P ** token g 1$m).

  Definition dtor_body (ret : val) (this : ptr) : WpSpec mpred val val :=
    (\pre{g P} this |-> R g 1$m P ** token g 1$m
     \post[ret] P).

  Definition lock_body (ret : val) (this : ptr) : WpSpec mpred val val :=
    (\prepost{q P g} this |-> R g q P
     \persist{thr} current_thread thr
     \pre{qt} not_locked this g thr qt
     \post[ret] P ** locked this g thr qt).

  Definition unlock_body (ret : val) (this : ptr) : WpSpec mpred val val :=
    (\prepost{q P g} this |-> R g q P
     \persist{thr} current_thread thr
     \pre{qt} locked this g thr qt
     \pre ▷P
     \post[ret] not_locked this g thr qt).

  (** [ret b] is returned on success ([b = true]) or failure. *)
  Definition try_lock_body (ret : bool -> val) (this : ptr) : WpSpec mpred val val :=
    (\prepost{q P g} this |-> R g q P
     \persist{thr} current_thread thr
     \pre{qt} not_locked this g thr qt
     \post{b}[ret b]
       if b then P ** locked this g thr qt
       else not_locked this g thr qt).

  (** * C++ member-function contracts *)

  Definition ctor_spec (this : ptr) : WpSpec mpred val val :=
    Reduce (ctor_body Vvoid this).

  Definition dtor_spec : ptr -> WpSpec mpred val val :=
    fun this => Reduce (dtor_body Vvoid this).

  Definition lock_spec_alt : ptr -> WpSpec mpred val val :=
    fun this => Reduce (lock_body Vvoid this).

  Definition unlock_spec_alt : ptr -> WpSpec mpred val val :=
    fun this => Reduce (unlock_body Vvoid this).

  Definition try_lock_spec_alt : ptr -> WpSpec mpred val val :=
    fun this => Reduce (try_lock_body Vbool this).
End with_cpp.
End base_mutex_spec.
