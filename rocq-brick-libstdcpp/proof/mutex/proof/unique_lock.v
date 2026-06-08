Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.spec.mutex.
Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock.

NES.Begin unique_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context `{HAS_THREADS : !HasStdThreads Σ}.

    Import R_unfold.

    Lemma default_ctor_spec_ok : verify[source] default_ctor_spec.
    Proof. verify_spec; go. Qed.

    cpp.spec "std::__addressof<std::mutex>(std::mutex&)" as __addressof_spec from source with (
      \arg{mp} "" (Vptr mp)
      \post[Vptr mp] emp
    ).

    #[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.

    Lemma mutex_defer_ctor_spec_ok : __addressof_spec |-- verify[source] mutex_defer_ctor_spec.
    Proof. verify_spec; go. by rewrite cQp.scale_mut right_id_L. Qed.

    (* #[local] Instance: `{SplitRecord (prod A B)} := {}. *)

    Lemma mutex_ctor_spec_alt_ok : __addressof_spec |-- verify[source] mutex_ctor_spec_alt.
    Proof.
      verify_spec; go.
      iExists (mp, g, q, P), K.
      rewrite cQp.scale_mut right_id_L.
      go.
    Qed.

  End with_cpp.
NES.End unique_lock.
