(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.algorithms.hints.
Require Import skylabs.brick.libstdcpp.test.algorithms.all_any_none_of_vector_cpp.

Require Import skylabs.auto.cpp.prelude.test.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : all_any_none_of_vector_cpp.source ⊧ σ}.

  #[local] Abbreviation alloc_int := (std.allocator.T "int").
  #[local] Abbreviation iter_int := (std.vector.iterator.T "int").

  (** The adapter dereferences the library iterator, so it relies on its <<operator*>>. *)
  #[local] Instance : std.IteratorDeps iter_int (std.vector.iterator.iter_deref false "int" alloc_int) := {}.

  #[local] Instance Positive_rep : BundledRep "Positive" unit :=
    {| objR q _ := structR "Positive" q |}.
  #[local] Instance Positive_pred : std.Predicate "Positive" unit Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 0)%Z).

  cpp.spec "Positive::operator()(int) const" as positive_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q} this |-> structR "Positive" q
     \post[Vbool (bool_decide (x > 0)%Z)] emp).

  Lemma positive_ok : verify[source] positive_spec.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "Positive::~Positive()" as positive_dtor_spec with
    (\this this
     \pre this |-> structR "Positive" 1$m
     \post emp).

  Lemma positive_dtor_ok : verify[source] positive_dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition positive_dtor_B := [LINK] positive_dtor_ok.
  #[local] Hint Resolve positive_dtor_B : sl_opacity.

  cpp.spec "TestVector()" as test_vector with
    (\persist positive_spec
     \persist std.vector.iterator.iter_deref false "int" alloc_int
     \post emp).
  Lemma test_vector_ok : verify[source] test_vector.
  Proof using MOD.
    verify_spec. go.
    iExists tt. go.
    iExists (std.vector.base_pointer st', 2%Z), (std.vector.base_pointer st', 0%Z). go.
  Qed.

  Definition positive_B := [LINK] positive_ok.
  Definition test_vector_B := [LINK] test_vector_ok.
  #[local] Hint Resolve positive_B test_vector_B : sl_opacity.

  cpp.spec "main()" as main_spec with
    (\persist positive_spec
     \persist std.vector.iterator.iter_deref false "int" alloc_int
     \post[Vint 0] emp).

  Lemma main_ok : verify[source] main_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition main_B := [LINK] main_ok.
  #[local] Hint Resolve main_B : sl_opacity.

  Lemma specs_ok :
    denoteModule source **
    ▷ ( std.vector.specs "int" alloc_int **
        std.vector.iterator.specs false "int" alloc_int **
        std.allocator.specs "int" **
        std.all_of_spec iter_int "Positive" source **
        std.cassert.specs )
    |-- main_spec.
  Proof using MOD.
    rewrite /std.vector.specs /std.vector.iterator.specs /std.allocator.specs /std.cassert.specs.
    work.
  Qed.
End with_cpp.
