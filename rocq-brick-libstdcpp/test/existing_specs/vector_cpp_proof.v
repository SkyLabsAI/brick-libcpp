
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import vector_cpp.

Require Import skylabs.brick.libstdcpp.lib.tactics.

Require Import skylabs.auto.cpp.proof.

Require Import skylabs.auto.cpp.prelude.proof.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : vector_cpp.source ⊧ σ}.

  cpp.spec "default_construction_oracle()" as default_construction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma default_construction_oracle_ok : verify[vector_cpp.source] "default_construction_oracle()".

Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.
    iExists (nullptr, 0), (nullptr, 0).
    go $usenamed=true.
  Qed.

  Require Import skylabs.brick.libstdcpp.allocator.spec.
  cpp.spec "allocator_construction_oracle()" as allocator_construction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma allocator_construction_oracle_ok : verify[vector_cpp.source] "allocator_construction_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.
    iExists ().
    go $usenamed=true.
    iExists (nullptr, 0), (nullptr, 0).
    go $usenamed=true.
  Qed.

  cpp.spec "copy_with_allocator_oracle()" as copy_with_allocator_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma copy_with_allocator_oracle_ok : verify[vector_cpp.source] "copy_with_allocator_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.
    iExists ().
    go $usenamed=true.
  Qed.

  cpp.spec "move_with_allocator_oracle()" as move_with_allocator_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma move_with_allocator_oracle_ok : verify[vector_cpp.source] "move_with_allocator_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.
    iExists ().
    go $usenamed=true.
  Qed.

  cpp.spec "sized_and_fill_construction_oracle()" as sized_and_fill_construction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma sized_and_fill_construction_oracle_ok : verify[vector_cpp.source] "sized_and_fill_construction_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.
    iExists ().
    go $usenamed=true.
    iExists ().
    go $usenamed=true.
    cbn in _H_0, H.
    cbv [replicateZ replicateN] in _H_0, H.
    cbv in _H_0, H.
    cbn in _H_0, H.
    match goal with
    | Hn : (0 <= ?n)%Z |- _ =>
        pose proof Hn as Hnonnegative
    end.
    change (3%N = Z.to_N (size0 - 0))%N in H.
    rewrite Z.sub_0_r in H.
    apply (f_equal Z.of_N) in H.
    rewrite (Z2N.id size0 Hnonnegative) in H.
    cbn in H.
    subst size0.
    match goal with
    | Hn : (0 <= ?n)%Z, Hlen : _ |- _ =>
        is_var n;
        change (3%N = Z.to_N (n - 0))%N in Hlen;
        rewrite Z.sub_0_r in Hlen;
        apply (f_equal Z.of_N) in Hlen;
        rewrite (Z2N.id n Hn) in Hlen;
        cbn in Hlen;
        subst n
    end.
    go $usenamed=true.
    cbv [replicateZ replicateN] in H.
    cbn in H.
    cbv in H.
    inversion H.
    go $usenamed=true.
    cbv [replicateZ replicateN] in H.
    cbv in H.
    inversion H.
    done.
  Qed.


cpp.spec "modifier_oracle()" as modifier_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma modifier_oracle_ok : verify[vector_cpp.source] "modifier_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

    iExists (std.vector.base_pointer st', 0), (std.vector.base_pointer st', 0).
    go $usenamed=true.
  Qed.
  cpp.spec "accessor_oracle()" as accessor_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma accessor_oracle_ok : verify[vector_cpp.source] "accessor_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

  Qed.

  cpp.spec "scoped_destruction_oracle()" as scoped_destruction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma scoped_destruction_oracle_ok : verify[vector_cpp.source] "scoped_destruction_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

  Qed.

  cpp.spec "resize_oracle()" as resize_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma resize_oracle_ok : verify[vector_cpp.source] "resize_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

    cbn in _H_21, _H_42.

    simpl in _H_21, _H_42.

    simpl [replicateZ] in _H_21, _H_42.

    cbv [replicateZ replicateN] in _H_21, _H_42.

    cbn in _H_21, _H_42.

    cbv in _H_21, _H_42.

    inversion _H_21; inversion _H_42; subst.
    go $usenamed=true.

  Qed.

  cpp.spec "iterator_oracle()" as iterator_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma iterator_oracle_ok : verify[vector_cpp.source] "iterator_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

    iExists (std.vector.base_pointer st', 1 + 1 + 1),
      (std.vector.base_pointer st', 1 + 1 + 1),
      (std.vector.base_pointer st', 1 + 1 + 1),
      (std.vector.base_pointer st', 1 + 1 + 1),
      (nullptr, 0), (nullptr, 0), (nullptr, 0), (nullptr, 0).
    go $usenamed=true.

  Qed.

  cpp.spec "copy_construction_oracle()" as copy_construction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma copy_construction_oracle_ok : verify[vector_cpp.source] "copy_construction_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

  Qed.

  cpp.spec "move_construction_oracle()" as move_construction_oracle_spec from vector_cpp.source with (
    \post[Vbool true] emp).

  Lemma move_construction_oracle_ok : verify[vector_cpp.source] "move_construction_oracle()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec.
    go $usenamed=true.

  Qed.

End with_cpp.

Lemma vector_index_at_size_precondition_unreachable (n : Z) :
  0 <= n -> ~ (0 <= n < n).
Proof. lia. Qed.

Lemma vector_empty_nonempty_precondition_unreachable :
  ~ (0 < (0 : Z)).
Proof. lia. Qed.
