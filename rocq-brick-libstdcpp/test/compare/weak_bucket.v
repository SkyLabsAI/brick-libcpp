(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Require Import skylabs.brick.libstdcpp.compare.pred.
Require Import skylabs.brick.libstdcpp.test.compare.test_cpp.

Record WeakBucket := {
  weak_bucket_key : Z;
}.
#[only(eq_dec)] derive WeakBucket.

#[global] Instance SplitRecord_WeakBucket : SplitRecord WeakBucket := {}.

Definition weak_bucket_bucket (p : WeakBucket) : Z :=
  Z.quot p.(weak_bucket_key) 10.

Definition weak_bucket_equivalent : relation WeakBucket :=
  option.on eq weak_bucket_bucket.

Definition weak_bucket_compare (p p' : WeakBucket) : comparison :=
  Z.compare (weak_bucket_bucket p) (weak_bucket_bucket p').


sl.lock
Definition WeakBucketR `{Σ : cpp_logic, σ : genv} (q : cQp.t) (p : WeakBucket) : Rep :=
  structR "WeakBucket" q **
  _field "WeakBucket::key" |-> primR Tint q (Vint p.(weak_bucket_key)).
#[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive WeakBucketR.


Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context `{MOD : test_cpp.source ⊧ σ}.

  cpp.spec "WeakBucket::~WeakBucket()" as weak_bucket_dtor with (
    \this this
    \pre{m} this |-> WeakBucketR 1$m m
    \post emp).

  cpp.spec "operator==(const WeakBucket&, const WeakBucket&)" as weak_bucket_eq with (
    \arg{lhs} "lhs" (Vref lhs)
    \arg{rhs} "rhs" (Vref rhs)
    \prepost{q_lhs lhs_m} lhs |-> WeakBucketR q_lhs lhs_m
    \prepost{q_rhs rhs_m} rhs |-> WeakBucketR q_rhs rhs_m
    \post[Vbool (bool_decide (weak_bucket_equivalent lhs_m rhs_m))] emp).

  cpp.spec "operator<=>(const WeakBucket&, const WeakBucket&)" as weak_bucket_spaceship with (
    \arg{lhs} "lhs" (Vref lhs)
    \arg{rhs} "rhs" (Vref rhs)
    \prepost{q_globals} std.compare.weak_ordering_globals q_globals
    \prepost{q_lhs lhs_m} lhs |-> WeakBucketR q_lhs lhs_m
    \prepost{q_rhs rhs_m} rhs |-> WeakBucketR q_rhs rhs_m
    \post{result}[Vptr result]
      result |-> std.compare.weak_orderingR 1$m (weak_bucket_compare lhs_m rhs_m)).

  Definition weak_bucket_specs :=
    weak_bucket_dtor **
    weak_bucket_eq **
    weak_bucket_spaceship.
  #[global] Hint Opaque weak_bucket_specs : typeclass_instances sl_opacity.
  #[only(knowledge)] derive weak_bucket_specs.

End with_cpp.
