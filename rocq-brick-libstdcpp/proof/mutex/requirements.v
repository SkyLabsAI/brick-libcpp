Require Import skylabs.auto.cpp.prelude.proof.

(** This file captures the following "named requirements":
    - [BasicLockable](https://cppreference.com/cpp/named_req/BasicLockable)
    - [Lockable](https://cppreference.com/cpp/named_req/Lockable)

    It proposes a pattern for capturing these using Rocq typeclasses such
    that clients can use these to depend on
 *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* NOTE: This is *not* meant to be a statement about the way that
     things should be packaged (bundled or unbundled), just a demonstration
     of the way that specifications can be written in a higher-order way.
   *)

  (** This captures [BasicLockable](https://cppreference.com/cpp/named_req/BasicLockable) *)
  Class BasicLockable (ty : type) {T : Type} (R : cQp.t -> T -> Rep) : Type :=
  { do_lock : ptr -> T -> mpred -> mpred
    (* the WP for <ty::lock()> *)
  ; do_unlock : ptr -> T -> mpred -> mpred
    (* the WP for <ty::unlock()> *)
  ; cfrac :> CFracSplittable_1 R }.

  Section with_BasicLockable.
    Context (ty : type) {T: Type} (R : cQp.t -> T -> Rep) {BL : BasicLockable ty R}.

    Definition lock_basic_lockable : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q m} this |-> R q m
       \pre{K} do_lock this m K
       \post K).

    Definition unlock_basic_lockable : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q m} this |-> R q m
       \pre{K} do_unlock this m K
       \post K).
  End with_BasicLockable.

  (** This captures [Lockable](https://cppreference.com/cpp/named_req/Lockable) *)
  Class Lockable (ty : type) {T : Type} (R : cQp.t -> T -> Rep) {BASIC_LOCKABLE : BasicLockable ty R} : Type :=
  { do_try_lock : ptr -> T -> (bool -> mpred) -> mpred }.

  Section with_Lockable.
    Context (ty : type) {T : Type} (R : cQp.t -> T -> Rep) `{LOCKABLE : Lockable (T:=T) ty R}.

    Definition try_lock_lockable : ptr -> WpSpec mpred val val :=
      (\this this
       \prepost{q m} this |-> R q m
       \pre{K} do_try_lock this m K
       \post{r}[Vbool r] K r).
  End with_Lockable.

End with_cpp.
