Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.memory_align.spec.
Require Import skylabs.brick.libstdcpp.test.memory_align.oracle_cpp.

#[local] Open Scope Z_scope.
#[local] Open Scope N_scope.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context `{MOD : oracle_cpp.module ⊧ σ}.

  cpp.spec "oracle_align(unsigned long, unsigned long, void*&, unsigned long&)"
    as oracle_align_spec from module with
    (\arg{alignment} "alignment" (Vn alignment)
     \arg{size} "size" (Vn size)
     \arg{ptr_cell} "ptr" (Vref ptr_cell)
     \arg{space_cell} "space" (Vref space_cell)
     \with p va space_before q
     \let skip := alignment_skipN alignment va
     \let success := aligned_block_fitsN alignment size va space_before
     \let aligned_p := (p : ptr) .[ Tuchar ! Z.of_N skip ]
     \let ptr_after := if success then aligned_p else p
     \let result := if success then aligned_p else nullptr
     \let va_after := if success then (va + skip)%N else va
     \let space_after := space_afterN alignment size va space_before
     \require mathematical_power_of_two (Z.of_N alignment)
     \prepost p |-> byte_bufferR q space_before
     \prepost p |-> pinnedR va
     \pre ptr_cell |-> primR "void*" 1$m (Vptr p) **
          space_cell |-> ulongR 1$m (Z.of_N space_before)
     \post[Vptr result]
       ptr_cell |-> primR "void*" 1$m (Vptr ptr_after) **
       space_cell |-> ulongR 1$m (Z.of_N space_after) **
       ptr_after |-> pinnedR va_after).

  Lemma oracle_align_ok : verify[module]
      "oracle_align(unsigned long, unsigned long, void*&, unsigned long&)".
  Proof.
    verify_spec.
    go $usenamed=true.
    iExists va, q.
    go $usenamed=true.
  Qed.
End with_cpp.
