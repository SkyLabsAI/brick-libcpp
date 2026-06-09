Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Require Export skylabs.brick.libstdcpp.runtime.pred.
Require Import skylabs.brick.libstdcpp.mutex.spec.prelude.
Require Import skylabs.brick.libstdcpp.mutex.spec.recursive_mutex.
Require Import skylabs.brick.libstdcpp.mutex.requirements.
Require Import skylabs.brick.libstdcpp.mutex.spec.unique_lock_recursive_mutex.

NES.Begin unique_lock.
  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.

    Context `{HAS_THREADS : !HasStdThreads Σ}.
    Context `{!recursive_mutex.lockedG Σ}.
    Context `{!HasOwn (iPropI _) recursive_mutex.cmraR}.

    Import R_unfold.

    Lemma default_ctor_spec_ok : verify[source] default_ctor_spec.
    Proof. verify_spec; go. Qed.

    cpp.spec "std::__addressof<std::recursive_mutex>(std::recursive_mutex&)" as __addressof_spec from source with (
      \arg{mp} "" (Vptr mp)
      \post[Vptr mp] emp
    ).

    #[local] Hint Resolve fractional.UNSAFE_read_prim_learn : sl_opacity.

    #[local] Instance: `{SplitRecord (M T)} := {}.

    Lemma lock_ctor_spec_ok :
    (* needed because [has_dependency] skips builtins *)
      __addressof_spec |--
      verify[source] lock_ctor_spec.
    Proof.
      verify_spec; go.
      iExists K, q', q; rewrite cQp.scale_mut right_id_L.
      go.
    Qed.

    Lemma lock_defer_ctor_spec_ok : __addressof_spec |-- verify[source] lock_defer_ctor_spec.
    Proof. verify_spec; go. by rewrite cQp.scale_mut right_id_L. Qed.

  End with_cpp.
NES.End unique_lock.
