Require Import skylabs.bi.tls_modalities.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.lib.lock_ghost2.
Require Import skylabs.brick.libstdcpp.thread.thread_hpp.

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
    Exclusive0 (this |-> R state).

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

  cpp.spec "std::thread::thread<void (*&)(), ...<>, void>(void (*&)())" as ctor_spec from source with
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
Section thread_id_specs.
  Parameter thread_idR : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t ->
    (* None if value is thread::id(), Some otherwise *)
    option thread_idT -> Rep.
  #[only(cfracsplittable, type_ptr="std::thread::id")] derive thread_idR.
  #[global] Axiom thread_idR_WeaklyObjective :
    ∀ `{Σ : cpp_logic, σ : genv} (q : cQp.t)
      (o : option thread_idT) (p : ptr),
      WeaklyObjective (thread_idR q o p).
  #[global] Existing Instance thread_idR_WeaklyObjective.

  Context `{Σ : cpp_logic} {σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  cpp.spec (default_ctor "std::thread::id")
      as thread_id_ctor_spec from source with (
    \this this
    \post this |-> thread_idR 1$m None).

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

  cpp.spec "std::this_thread::get_id()" as get_id_spec from source with (
    \persist{thr} current_thread thr
    \post{result}[Vptr result]
      result |-> thread_idR 1$m (Some thr)).

  cpp.spec "std::this_thread::yield()" as yield_spec from source with (
    \post emp).
End thread_id_specs.
