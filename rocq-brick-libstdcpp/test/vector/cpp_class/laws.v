Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.string.pred.
Require skylabs.brick.libstdcpp.test.vector.cpp_class.test_cpp.
#[local] Abbreviation source := test_cpp.source.

Section S.
  Context `{Σ : cpp_logic} {σ : genv}.
  #[local] Abbreviation S := (std.vector.spineR "unsigned long" "std::allocator<unsigned long>").
  Goal forall sz st, CFractional (fun q => S q sz st).
  Proof. intros. first [ apply _; idtac "spineR CFractional: found" | idtac "spineR CFractional: NOT found" ]. Abort.
  Goal forall q sz st, Timeless (S q sz st).
  Proof. intros. first [ apply _; idtac "spineR Timeless: found" | idtac "spineR Timeless: NOT found" ]. Abort.
  Goal CFracValid2 S.
  Proof. first [ apply _; idtac "spineR CFracValid2: found" | idtac "spineR CFracValid2: NOT found" ]. Abort.
  Goal forall xs : list Z, CFractional (fun q => std.vector.R_alloc "unsigned long" "std::allocator<unsigned long>" q xs).
  Proof. intros. Timeout 1 apply _. Qed.
End S.
