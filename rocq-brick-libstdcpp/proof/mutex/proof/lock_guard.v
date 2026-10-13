Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.lock_guard.

Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.
  Context `{MUTEX_SETS : !mutex_set_G Σ}.
  Context `{!mutex.G Σ}.

  Import lock_guard.
  Import R_unfold.

  (* TODO: not ideal *)
  #[global] Instance UNSAFE_R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> learn_eq ==> learn_eq ==> fin_at) mutex.R).
  Proof. solve_learnable. Qed.

  #[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.
  #[local] Instance: `{SplitRecord (M T)} := {}.

  (* std::mutex ctor implies lock_guard<std::mutex> ctor *)
  Lemma ctor_ok :
    denoteModule source **
    mutex.lock_spec 
    |-- lock_guard.ctor_spec "std::mutex" source.
  Proof.
    verify_spec.
    go.
    iExists K, t.
    go with br_erefl.
    by rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
  Qed.

  (* std::mutex dtor implies lock_guard<std::mutex> dtor *)
  Lemma dtor_ok : verify[source] "std::lock_guard<std::mutex>::~lock_guard()".
  Proof.
    verify_spec.
    rewrite !R.unlock.
    go.
    iExists K, t.
    go with br_erefl.
    by rewrite cQp.scale_mut (right_id_L 1%Qp Qp.mul).
  Qed.

End with_cpp.
