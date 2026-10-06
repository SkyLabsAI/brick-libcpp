Require Import skylabs.bi.tls_modalities.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.thread.thread_hpp.

Import linearity.

(** Specs for thread creation and joining. *)
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{!MutexSets.G Σ}.

  (** Exclusive ownership of a thread object.
      [R $ None] is already joined thread and non-joinable;
      [R $ Some (child, Q)] is a handle to join [child] and receive [Q].
      R would require the mpred to be WeaklyObjective. *)
  Parameter R : option (thread_idT * mpred) -> Rep.
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(type_ptr="std::thread")] derive R.
  #[global] Declare Instance R_exclusive state (this : ptr) :
    Exclusive0 (R state).

  (** The mutex-set map tracks spawned thread IDs and supplies each child
      with its [MutexSets.my_mutexes] handle. *)
  Definition spawned_threads_inv (N : namespace) (γ : iprop.gname) : mpred :=
    inv N (Exists tids, MutexSets.mutex_set_map γ tids).

  Lemma spawned_threads_inv_alloc N :
    ⊢ |={⊤}=> ∃ γ, spawned_threads_inv N γ.
  Proof.
    iMod MutexSets.alloc_mutex_set_map as (γ) "Hmap".
    iMod (inv_alloc N _ (Exists tids, MutexSets.mutex_set_map γ tids)
      with "[Hmap]") as "Hinv".
    { iNext. iExists ∅. done. }
    iModIntro. iExists γ. done.
  Qed.

  Definition entry_type : type := Tfunction (FunctionType Tvoid []).

  #[global] Declare Instance wp_fptr_objective (f : ptr) (Q : mpred)
      `{!WeaklyObjective Q} :
    ObjectiveWith threadTI
      (wp_fptr (σ.(genv_tu).(types)) entry_type f [] (fun _ => Q)).

  (* TODO should have a generic thread spawn spec that one can pass any resrouce
     to, and does not mention my_mutex. *)
  (** Passing a function lvalue binds a function reference directly, without
      an intermediate function-pointer object. The child receives its mutex
      namespace pool before running the entry point. Resources that the entry
      point returns can be included in [Q] and recovered by joining. *)
  Definition spawn_spec_body : ptr -> WpSpec mpred val val :=
    (\this this
     \arg{f : ptr} "f" (Vptr f)
     \pre{N γ} spawned_threads_inv N γ
     \persist{parent} current_thread parent
     \pre{Q : mpred} [| WeaklyObjective Q |]
     \pre
       (∀ child,
          (MutexSets.my_mutexes γ child (coPset.CoPset ⊤) -*
          (* FIXME is the usage of this wp_fptr correct? *)
          wp_fptr (σ.(genv_tu).(types)) entry_type f []
              (* f returns void so Q does not depend on return value *)
              (fun _ => Q)))
     \post Exists child,
       [| child <> parent |] ** this |-> R (Some (child, Q))).

  (** Must be joinable, takes resource and leaves the object non-joinable. *)
  Definition join_spec_body : ptr -> WpSpec mpred val val :=
    (\this this
     \persist{parent} current_thread parent
     \pre{child Q} this |-> R (Some (child, Q))
     (* error if joining itself *)
     \require child <> parent
     \post this |-> R None ** Q).

  cpp.spec "std::thread::thread<void ( *&)(), ...<>, void>(void ( *&)())" as ctor_spec from source with
      (\exact Reduce spawn_spec_body).

  cpp.spec "std::thread::thread<void (&)(), ...<>, void>(void (&)())"
      as ctor_ref_spec from source with
      (\exact Reduce spawn_spec_body).

  (** Must be joined (and resources transferred) so can be destroyed. *)
  cpp.spec "std::thread::~thread()" as dtor_spec from source with
      (\this this
       \pre this |-> R None
       \post emp).

  cpp.spec "std::thread::join()" as join from source with
      (\exact Reduce join_spec_body).
End with_cpp.

(** Specifications for thread IDs and the current thread's operations. *)
Module thread_id_specs.
  (* Assume thread_idT can project an integer. *)
  Parameter thread_id_to_Z : thread_idT -> Z.
  (* Underlying integer of a thread ID object is unique. *)
  Axiom thread_id_to_Z_injective : 
    forall x y, thread_id_to_Z x = thread_id_to_Z y -> x = y.
  (* Value of thread::id(). Does not represent any thread. *)
  Parameter default_thread_id : thread_idT.

  (* Assume some injective hash function. *)
  Parameter thread_id_hash : thread_idT -> Z.
  Axiom thread_id_hash_injective : 
    forall x y, thread_id_hash x = thread_id_hash y -> x = y.

  (* we know there is only one field in the implementation; we expose it here.
    FIXME or should we abstract it away? *)
  sl.lock
  Definition thread_idR `{Σ : cpp_logic, σ : genv} (q : cQp.t)
      (tid : thread_idT) : Rep :=
    structR "std::thread::id" q **
    _field "std::thread::id::_M_thread" |-> ulongR q (thread_id_to_Z tid).
  #[only(type_ptr,cfractional,ascfractional,timeless)] derive thread_idR.

  (** Weak objectivity of thread-ID storage, as required by invariant clients. *)
  #[global] Axiom thread_idR_WeaklyObjective :
    ∀ `{Σ : cpp_logic, σ : genv} (q : cQp.t) (tid : thread_idT) (p : ptr),
      WeaklyObjective (thread_idR q tid p).
  #[global] Existing Instance thread_idR_WeaklyObjective.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec (default_ctor "std::thread::id")
      as thread_id_ctor_spec from source with (
    \this this
    \post this |-> thread_idR 1$m default_thread_id).

  cpp.spec (const_copy_ctor "std::thread::id")
      as thread_id_copy_ctor_spec from source with (
    \this this
    \arg{other} "" (Vptr other)
    \prepost{q o} other |-> thread_idR q o
    \post this |-> thread_idR 1$m o).

  cpp.spec (dtor "std::thread::id") as thread_id_dtor_spec from source with (
    \this this
    \pre{o} this |-> thread_idR 1$m o
    \post emp).

  cpp.spec "std::thread::id::operator=(const std::thread::id&)"
      as thread_id_copy_assign_spec from source with (
    \this this
    \arg{other} "" (Vptr other)
    \pre{old} this |-> thread_idR 1$m old
    \prepost{q o} other |-> thread_idR q o
    \post[Vref this] this |-> thread_idR 1$m o).

  cpp.spec "std::thread::id::operator=(std::thread::id&&)"
      as thread_id_move_assign_spec from source with (
    \this this
    \arg{other} "" (Vptr other)
    \pre{old} this |-> thread_idR 1$m old
    \prepost{o} other |-> thread_idR 1$m o
    \post[Vref this] this |-> thread_idR 1$m o).

  cpp.spec "std::operator==(std::thread::id, std::thread::id)"
      as thread_id_eq_spec from source with (
    \arg{lhs} "" (Vptr lhs)
    \arg{rhs} "" (Vptr rhs)
    \prepost{q1 o1} lhs |-> thread_idR q1 o1
    \prepost{q2 o2} rhs |-> thread_idR q2 o2
    \post[Vbool (bool_decide (o1 = o2))] emp).

  (** [thread.thread.this] guarantees a running thread has a non-default ID. *)
  cpp.spec "std::this_thread::get_id()" as get_id_spec from source with (
    \persist{th} current_thread th
    \post{result}[Vptr result]
      result |-> thread_idR 1$m th ** [| th <> default_thread_id |]).

  #[global] Instance thread_idR_learn :
    Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) thread_idR).
  Proof. solve_learnable. Qed.

  Definition thread_id_layout := Eval vm_compute in types source !! "std::thread::id"%cpp_name.

  #[program]
  Definition thread_id_const_C (tu : translation_unit) (p : ptr) :=
    \cancelx
    \consuming{owner from} p |-> thread_idR from owner
    \guard (types tu !! "std::thread::id"%cpp_name =[Vm?]=> thread_id_layout)
    \proving{to Q} wp_const tu from to p "std::thread::id" Q
    \through (p |-> thread_idR to owner -* Q)
    \end@{mpredI}.
  Next Obligation.
    intros. rewrite thread_idR.unlock !_at_sep.
    iIntros "[Hstruct Hfield]" (to Q) "HQ".
    iApply (wp_const_named_struct from to _ _ _ _ G with "Hstruct").
    cbn. work $usenamed=true with br_erefl.
  Qed.

  (** The callable returns the thread-ID hash. Its implementation is verified
      against the byte-hash primitive below. *)
  cpp.spec "std::hash<std::thread::id>::operator()(const std::thread::id&) const"
      as hash_spec from source with (
    \this this
    \arg{value} "__id" (Vptr value)
    \persist type_ptr "std::hash<std::thread::id>" this
    \prepost{q owner} value |-> thread_idR q owner
    \post[Vint (thread_id_hash owner)] emp).

  (** Hash-object destruction, including its empty base object. *)
  cpp.spec "std::__hash_base<unsigned long, std::thread::id>::~__hash_base()"
      as hash_base_dtor_spec from source with (
    \this this
    \pre this |-> structR "std::__hash_base<unsigned long, std::thread::id>" 1$m
    \post emp).

  cpp.spec "std::hash<std::thread::id>::~hash()"
      as hash_dtor_spec from source with (
    \this this
    \pre this |-> structR "std::hash<std::thread::id>" 1$m
    \pre this ,, _base "std::hash<std::thread::id>"
      "std::__hash_base<unsigned long, std::thread::id>" |->
      structR "std::__hash_base<unsigned long, std::thread::id>" 1$m
    \post emp).

  cpp.spec "std::this_thread::yield()" as yield_spec from source with (
    \post emp).
End with_cpp.
#[global] Hint Resolve thread_id_const_C : sl_opacity.

(** NOTE that the hash specs and proofs are all generated by AI.
   [hash_bytes_spec] cannot be verified because the spec for
   <<__builtin_memcpy>> is missing. Maybe cleaner to just axiomatize
   [hash_ulong_spec] and remove the rest. *)
Section hash_proofs.
  Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ}.

  cpp.spec "std::_Hash_bytes(const void*, unsigned long, unsigned long)"
      as hash_bytes_spec from source with (
    \arg{value} "__ptr" (Vptr value)
    \arg "__len" (Vint 8)
    \arg "__seed" (Vint 3339675911)
    \prepost{q owner} value |-> ulongR q (thread_id_to_Z owner)
    \post[Vint (thread_id_hash owner)] emp).

  cpp.spec "std::_Hash_impl::hash(const void*, unsigned long, unsigned long)"
      as hash_impl_spec from source with (
    \arg{value} "__ptr" (Vptr value)
    \arg "__clength" (Vint 8)
    \arg "__seed" (Vint 3339675911)
    \prepost{q owner} value |-> ulongR q (thread_id_to_Z owner)
    \post[Vint (thread_id_hash owner)] emp).

  cpp.spec "std::_Hash_impl::hash<unsigned long>(const unsigned long&)"
      as hash_ulong_spec from source with (
    \arg{value} "__val" (Vptr value)
    \prepost{q owner} value |-> ulongR q (thread_id_to_Z owner)
    \post[Vint (thread_id_hash owner)] emp).

  Section with_hash_module.
    Context `{MOD : source ⊧ σ}.

    Lemma hash_impl_ok : verify[source] hash_impl_spec.
    Proof using MOD. verify_spec; go. iExists owner. go. Qed.

    Lemma hash_ulong_ok : verify[source] hash_ulong_spec.
    Proof using MOD. verify_spec; go. iExists owner. go. Qed.

    Lemma hash_ok : verify[source] hash_spec.
    Proof using MOD.
      verify_spec. rewrite thread_idR.unlock. go. iExists owner. go.
      rewrite thread_idR.unlock. go.
    Qed.

    Lemma hash_base_dtor_ok : verify[source] hash_base_dtor_spec.
    Proof using MOD. verify_spec; go. Qed.

    Lemma hash_dtor_ok : hash_base_dtor_spec |--
      verify[source] hash_dtor_spec.
    Proof using MOD. verify_shift; go. iModIntro. go. Qed.

    Lemma hash_link :
      denoteModule source ** hash_bytes_spec |--
      hash_spec ** hash_base_dtor_spec ** hash_dtor_spec.
    Proof using MOD.
      work.
      wapply hash_ok.
      wapply hash_ulong_ok.
      wapply hash_impl_ok.
      wapply hash_dtor_ok.
      wapply hash_base_dtor_ok.
      work $usenamed=true.
    Qed.
  End with_hash_module.
End hash_proofs.
End thread_id_specs.
