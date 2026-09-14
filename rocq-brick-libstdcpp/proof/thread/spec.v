Require Import skylabs.bi.tls_modalities.
Require Import skylabs.auto.cpp.prelude.proof.
(* Require Export skylabs.brick.libstdcpp.thread.pred. *)
Require Import skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.thread.thread_hpp.

(** Specifications for the nullary function-pointer specialization of
    <<std::thread>>. [spawn_spec] is the constructor contract, to be bound to
    the constructor specialization in the client's translation unit. The
    forwarding-reference argument points to a function-pointer object; the
    constructor copies its value before starting the child.

    These are normal-return contracts. They do not specify creation failures,
    arbitrary callable objects, argument decay/copying, or detach. *)
Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  (** Exclusive ownership of a thread object. [None] is non-joinable;
      [Some (child, Q)] owns the right to join [child] and receive [Q],
      interpreted in that child's thread context. In particular, this
      predicate must not be declared persistent or fractionally splittable. *)
  Parameter R : option (thread_idT * mpred) -> Rep.
  #[global] Hint Opaque R : sl_opacity typeclass_instances.
  #[only(type_ptr="std::thread")] derive R.
  #[global] Declare Instance R_exclusive state (this : ptr) :
    Exclusive0 (this |-> R state).

  Definition entry_type : type := Tfunction (FunctionType Tvoid []).

  (** The obligation is linear: resources needed by the child are consumed
      at spawn. Quantification allows the runtime to choose the child's ID.
      The modality prevents the parent's thread-local facts from being
      silently reused in the child. *)
  Definition spawn_spec : ptr -> WpSpec mpred val val :=
    (\this this
     \arg{fp : ptr} "f" (Vptr fp)
     \prepost{q f} fp |-> primR (Tptr entry_type) q (Vptr f)
     \persist{parent} current_thread parent
     \pre{Q : thread_idT -> mpred}
       (∀ child, [| child <> parent |] -*
         @(threadTI, child)
           (wp_fptr (σ.(genv_tu).(types)) entry_type f []
             (fun _ => Q child)))
     \post Exists child,
       [| child <> parent |] ** this |-> R (Some (child, Q child))).

  (** Joining consumes the join right exactly once and leaves the object
      non-joinable. Keep the child's modality on [Q]: join does not turn
      child-local ownership into ownership local to the caller. *)
  Definition join_spec : ptr -> WpSpec mpred val val :=
    (\this this
     \persist{parent} current_thread parent
     \pre{child Q} this |-> R (Some (child, Q))
     \require child <> parent
     \post this |-> R None ** @(threadTI, child) Q).

  (** Supply the instantiated constructor name from the translation unit. *)
    cpp.spec "std::thread::thread()" as ctor_spec with
      (\exact Reduce spawn_spec).

  Definition join : mpred :=
    specify {| info_name := "std::thread::join()";
               info_type := tMethod "std::thread" QM "void" [] |} join_spec.
End with_cpp.
