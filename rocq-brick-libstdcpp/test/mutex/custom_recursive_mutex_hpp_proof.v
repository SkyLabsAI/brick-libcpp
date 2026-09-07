(** Provisional *)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.brick.libstdcpp.test.mutex.custom_recursive_mutex_hpp.
(*
TODO step 1:

split recursive_mutex specs:

* C++- independent predicates vs
* what's bound to C++ names

* step2
specs for atomic

* step3???

 *)
Module custom_recursive_mutex.
  Abbreviation N := "MyRecursiveMutex"%cpp_name.

  (*
  sl.lock
  Definition countR `{Σ : cpp_logic, σ : genv} (count : nat) : Rep :=
    (* structR "std::recursive_mutex" 1$m ** *)
    _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m count. *)

  Parameter atomic_thread_idT : ∀ `{Σ : cpp_logic, σ : genv}, cQp.t -> option thread_idT -> Rep.

  Parameter exclusive_token : ∀ `{Σ : cpp_logic}, iprop.gname -> mpred.

  Record gname : Set := MkGname
  { lock_gname : iprop.gname
  ; cinv_gname : iprop.gname
  ; excl_gname : iprop.gname
  ; rec_gname : recursive_mutex.gname
  }.

  Definition lock_namespace : namespace := nroot .@@ "MyRecursiveMutex".
  (* About cinv. *)
  Parameter count_auth : ∀ `{Σ : cpp_logic} (count : nat), mpred.
  Parameter count_frag : ∀ `{Σ : cpp_logic} (count : nat), mpred.

  (* Definition IR `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !recursive_mutex.lockedG Σ} (γ : gname) (q : cQp.t) : mpred :=
    ∃ x, recursive_mutex.owned_count_id_auth γ.(rec_gname) x. *)
(*
    Definition rawR `{Σ : cpp_logic, σ : genv} (owner : option thread_idT) (count : nat) : Rep :=
      structR "std::recursive_mutex" 1$m **
      _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m count. *)

  Section with_Σ.
    Context `{Σ : cpp_logic, σ : genv, !HasStdThreads Σ, !recursive_mutex.lockedG Σ}.

    Definition mutex_content (γ : gname) : Rep :=
      ∃ count,
         _field "MyRecursiveMutex::m_count" |-> ulonglongR 1$m (Z.of_nat count) **
        pureR (
          count_auth count
          (* **
          exclusive_token γ.(excl_gname) *)
          ) .

  Definition IR (γ : gname) (q : cQp.t) : Rep :=
    structR N q$m **
    (* TODO: mutex could take a [Rep] to save us this [as_Rep] *)
    as_Rep (fun this =>
      this ,, _field "MyRecursiveMutex::m_lock" |-> mutex.R γ.(lock_gname) q
        (this |-> mutex_content γ) **
      (* *)
      (this |-> mutex_content γ
      (* ** recursive_mutex.token γ.(rec_gname) (* ? *) *)
      \\//
      exclusive_token γ.(excl_gname)
      (* ** recursive_mutex.given_token γ.(rec_gname) (* ? *) *)
      ) **
      cinv lock_namespace γ.(cinv_gname) (∃ count owner,
        count_frag count **
        this ,, _field "MyRecursiveMutex::m_owner" |-> atomic_thread_idT 1$m owner **
        recursive_mutex.owned_count_id_auth γ.(rec_gname) ((λ t, (t, Nat.pred count)) <$> owner) **
        [| owner = None <-> count = 0 |] **
        match count with
        | 0 => emp
        | _ => exclusive_token γ.(excl_gname)
        end)).
    (* we hold the lock if the owner is not none! *)
  End with_Σ.

End custom_recursive_mutex.
