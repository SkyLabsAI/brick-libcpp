(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.pthread.pred.
Require Import skylabs.brick.libstdcpp.pthread.spec.
Require Import skylabs.auto.cpp.prelude.spec.

Section with_cpp.
  Import pthread.
  Import auto.telescopes auto.telescopes.TeleNotations.

  Context `{Σ : cpp_logic, σ : genv}.
  Context `{!HasStdThreads Σ}.

  Class ThreadFunction (nm : globname) (P : mpred)
      (argT stateT : tele)
      (Pre : ptr -> argT -> mpred)
      (Post : ptr -> argT -> ptr -> mpred)
      (Post_c : ptr -> argT -> stateT -> mpred) :=
    thread_function : P |-- _global nm |-> unmaterialized_specR starter_kind (starter_spec _ _ Pre Post Post_c).
  #[global] Hint Mode ThreadFunction + + - - - - - : typeclass_instances.

  #[program]
  Definition fptr_spec_C P nm argT' stateT' Pre' Post' Post_c' :=
    \cancelx
    \using P
    \guard ThreadFunction nm P argT' stateT' Pre' Post' Post_c'
    \bound argT stateT Pre Post Post_c
    \proving _global nm |-> starter_specR argT stateT Pre Post Post_c
    \let P0 := fun t => ptr → tele_arg t → mpred
    \let P1 := fun t => ptr → tele_arg t → ptr → mpred
    \let P2 := fun t0 t1 => ptr -> tele_arg t0 → tele_arg t1 → mpred
    (* \let x := existT (P := fun t => ptr → tele_arg t → ptr → mpred) argT  *)
    (* \through [|  = existT argT' Pre' |] *)
    \through [| existT (P := P0) argT Pre = existT argT' Pre' |]
    \through [| existT (P := P1) argT Post = existT argT' Post' |]
    \through [| existT (P := fun x => sigT (P2 x)) argT (existT (P := P2 _) stateT Post_c) =
                existT argT' (existT stateT' Post_c') |]
    \end.
  Admit Obligations.

  #[program]
  Definition exists_tele_app_B {PROP : bi} {t : tele} (P : t -pt> PROP) :=
    \cancelx
    \bound_existential x
    \proving tele_app P x
    \through (∃p.. a, {instantiate x := a} ∗ tele_app P a)%I
    \end.
  Admit Obligations.

  #[program]
  Definition exists_tele_app_boxed_F {PROP : bi} {t : tele} (P : t -pt> PROP) x `{!IsAnyVariable x} :=
    \fwd
    \using □ tele_app P x
    \deduce (∃p.. a, [| x = a |] ∗ tele_app P a)%I
    \end.
  Admit Obligations.
  #[program]
  Definition exists_tele_app_F {PROP : bi} {t : tele} (P : t -pt> PROP) x `{!IsAnyVariable x} :=
    \fwd
    \using tele_app P x
    \deduce (∃p.. a, [| x = a |] ∗ tele_app P a)%I
    \end.
  Admit Obligations.

End with_cpp.

#[global] Hint Resolve fptr_spec_C : br_hints.
#[global] Hint Resolve exists_tele_app_B : br_hints.
#[global] Hint Resolve exists_tele_app_F | 1 : br_hints.
#[global] Hint Resolve exists_tele_app_boxed_F | 0 : br_hints.
