(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.cpp.spec.argr.

Require Import skylabs.brick.libstdcpp.thread.inc_hpp.
Require Import skylabs.brick.libstdcpp.thread.defs.
Require Import skylabs.brick.libstdcpp.thread.fptr.

Require Export skylabs.brick.libstdcpp.thread.prelude.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context {HAS_THREADS : HasStdThreads Σ}.

  Fixpoint flatten_Apack (xs : list temp_arg) : list type :=
    match xs with
    | [] => []
    | Atype ty :: xs => ty :: flatten_Apack xs
    | _ :: xs => flatten_Apack xs
    end.

  Fixpoint arg_list (args : list type) (spec : list ptr -> WpSpec mpredI ptr ptr) : WpSpec mpredI ptr ptr :=
    match args with
    | [] => spec []
    | ty :: tys  =>
        \arg{p0} "x" (p0 :> ptr)
          match mtype ty, ty with
          | Some (_, ty'), Tptr _
          | Some (_, ty'), Tref _
          | Some (_, ty'), Trv_ref _ =>
             \exact arg_list tys (fun ps => spec (p0 :: ps))
          | Some (_, ty'), _ =>
             \pre{v} p0 |-> primR ty' 1$m v
             \post* p0 |-> anyR ty' 1$m
             \exact arg_list tys (fun ps => spec (p0 :: ps))
          | None, _ =>
             \exact arg_list tys (fun ps => spec (p0 :: ps))
          end
    end.

  (* the variadic constructor is not in the AST because variadic templates are not supported *)
  Definition ctor_spec T Ts {args}
      (Ts' := map (trv_ref QM) (flatten_Apack Ts))
     `{!force.force list Ts' =[Whd+]=> mret args} :=
    specify.template.materialized_ctor "std::thread" [Atype (Tref T);Apack Ts;Atype Tvoid] (Tref T :: args) $
      \this this
      \arg{fnp} "fn" (fnp :> ptr)
      \let T' := erase_qualifiers T
      \prepost{fn} fnp |-> refR<T'> 1$m fn
      \pre False
      \with s
      \pre fn |-> cptrR s
      \exact arg_list args $ fun ps =>
        \pre{Q} precondition_of s args ps (fun POST0 POST1 => [| Q = (POST0 ∗ bi_exist POST1) |])
        \postR ∃ γ, this |-> thread.R  γ 1$m (Some Q).

  #[global] Hint Opaque ctor_spec : sl_opacity.
  Definition SpecFor_ctor := RegisterSpec ctor_spec.
  #[global] Existing Instance SpecFor_ctor.

  cpp.spec "std::thread::join()"
     as join_spec
     from inc_hpp.source
     with
     ( \this this
       \pre{γ Q} this |-> thread.R γ 1$m (Some Q)
       \post*    this |-> thread.R γ 1$m None
       \post Q ).

  cpp.spec "std::thread::detach()"
     as detach_spec
     from inc_hpp.source
     with
     ( \this this
       \pre{γ Q} this |-> thread.R γ 1$m (Some Q)
       \post*    this |-> thread.R γ 1$m None
       \post emp ).

  cpp.spec "std::thread::~thread()"
     as dtor_spec
     from inc_hpp.source
     with
     ( \this this
       \pre{γ} this |-> thread.R γ 1$m None
       \post emp ).

End with_cpp.
