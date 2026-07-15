Require Import skylabs.auto.cpp.prelude.pred.
Require Import skylabs.cpp.array.
Require Import skylabs.cpp.slice.

Require Export skylabs.brick.libstdcpp.memory_align.model.

#[local] Open Scope Z_scope.

(** [byte_bufferR q space] owns the caller-supplied contiguous byte storage.
    The bytes are intentionally abstract because [std::align] never reads or
    writes their contents. *)
sl.lock
Definition byte_bufferR `{Σ : cpp_logic} {σ : genv}
    (q : cQp.t) (space : N) : Rep :=
  array_sliceR Tuchar 0 (Z.of_N space)
    (fun _ : unit => anyR Tuchar q)
    (replicateZ (Z.of_N space) tt).

#[only(lazy_unfold)] derive byte_bufferR.
