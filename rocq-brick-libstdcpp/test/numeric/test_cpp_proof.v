
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.numeric.spec.
Require Import skylabs.brick.libstdcpp.test.numeric.test_cpp.

#[global] Hint Extern 10 (gcd_callable _ _ _) => vm_compute : pure.
#[global] Hint Extern 10 (lcm_callable _ _ _) => vm_compute : pure.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_gcd_int()" default.
  Lemma test_gcd_int_ok : verify[module] "test_gcd_int()".
  Proof.
    verify_spec; go $usenamed=true.
    have Hgcd : gcd 0 (0 - 27) = 27 by vm_compute.
    have Hcall : gcd_callable signed32_range 0 (0 - 27) by vm_compute.
    rewrite Hgcd. go $usenamed=true.
  Qed.

  cpp.spec "test_lcm_int()" default.
  Lemma test_lcm_int_ok : verify[module] "test_lcm_int()".
  Proof.
    verify_spec; go $usenamed=true.
    have Hlcm : model.lcm (0 - 27) 0 = 0 by vm_compute.
    have Hcall : lcm_callable signed32_range (0 - 27) 0 by vm_compute.
    rewrite Hlcm. go $usenamed=true.
  Qed.

  cpp.spec "test_mixed_width()" default.
  Lemma test_mixed_width_ok : verify[module] "test_mixed_width()".
  Proof.
    verify_spec; go $usenamed=true.
    have Hgcd : gcd (0 - 48) 18 = 6 by vm_compute.
    have Hcall : gcd_callable signed64_range (0 - 48) 18 by vm_compute.
    rewrite Hgcd. go $usenamed=true.
  Qed.

End with_cpp.
(* Bootstrap file; substantive edits are made through the live rocq-ed session. *)
