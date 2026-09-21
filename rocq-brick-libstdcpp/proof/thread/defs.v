(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.brick.libstdcpp.thread.prelude.
Require Export skylabs.brick.libstdcpp.runtime.pred.

Require Export skylabs.brick.libstdcpp.thread.inc_hpp.

Module thread.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** Fractional ownership of a <<std::mutex>> guarding the predicate <<P>>. *)
  Parameter R : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> cQp.t -> option mpred -> Rep.
  #[only(cfractional,cfracvalid,ascfractional,type_ptr="std::mutex")] derive R.
  #[global] Declare Instance R_learnable : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv},
      Cbn (Learn (learn_eq ==> any ==> learn_eq ==> learn_hints.fin) R).

  (** Owning [mutex_token γ 1] proves that the mutex is not locked, and
  therefore can be safely destroyed: the standard specifies that calling
  [std::mutex::~mutex()] while holding the lock results in undefined behavior.
  *)
  Parameter token : forall {HAS_THREADS : HasStdThreads Σ} {σ : genv}, gname -> Qp -> mpred.
  #[only(fractional,fracvalid,asfractional,timeless)] derive token.

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    #[global] Instance repfor `{!HasStdThreads Σ} {σ : genv} :
      rep.RepFor.C "std::mutex" [ArgType.Constant _; ArgType.CFrac; ArgType.Constant _]
        (funI γ q P => R γ q P ∗ pureR (token γ q)) := {}.
  End with_RepFor.

End with_cpp.
End thread.
