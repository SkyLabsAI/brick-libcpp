Require Import skylabs.auto.cpp.prelude.spec.

Require Export skylabs.brick.libstdcpp.memory_align.pred.
Require Import skylabs.brick.libstdcpp.memory_align.inc_memory_align_cpp.

#[local] Open Scope Z_scope.
#[local] Open Scope N_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, inc_memory_align_cpp.source ⊧ σ}.

  cpp.spec "std::align(unsigned long, unsigned long, void*&, unsigned long&)"
    as align_spec with
    (\arg{alignment} "__align" (Vn alignment)
     \arg{size} "__size" (Vn size)
     \arg{ptr_cell} "__ptr" (Vref ptr_cell)
     \arg{space_cell} "__space" (Vref space_cell)
     \with p va space q
     \let skip := alignment_skipN alignment va
     \let success := aligned_block_fitsN alignment size va space
     \let aligned_p := (p : ptr) .[ Tuchar ! Z.of_N skip ]
     \let ptr_after := if success then aligned_p else p
     \let result := if success then aligned_p else nullptr
     \let va_after := if success then (va + skip)%N else va
     \let space_after := space_afterN alignment size va space
     \require mathematical_power_of_two (Z.of_N alignment)
     \prepost p |-> byte_bufferR q space
     \prepost p |-> pinnedR va
     \pre ptr_cell |-> primR "void*" 1$m (Vptr p) **
          space_cell |-> ulongR 1$m (Z.of_N space)
     \post[Vptr result]
       ptr_cell |-> primR "void*" 1$m (Vptr ptr_after) **
       space_cell |-> ulongR 1$m (Z.of_N space_after) **
       ptr_after |-> pinnedR va_after).
End with_cpp.
