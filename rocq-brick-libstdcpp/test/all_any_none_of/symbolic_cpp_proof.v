(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.all_any_none_of.spec.
Require Import skylabs.brick.libstdcpp.test.all_any_none_of.symbolic_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  cpp.spec "symbolic_is_nonzero(unsigned char)" as symbolic_is_nonzero_spec
    from symbolic_cpp.source with
    (\arg{x} "byte" (Vint x)
     \post{r : bool}[Vbool r]
       [| r = bool_decide (x <> 0)%Z |]).

  Lemma symbolic_is_nonzero_ok :
    verify[symbolic_cpp.source] symbolic_is_nonzero_spec.
  Proof. verify_spec; go. Qed.

  Lemma symbolic_is_nonzero_predicate_spec (xs : list Z) :
    symbolic_is_nonzero_spec |--
      _global "symbolic_is_nonzero(unsigned char)" |->
        cptrR (all_any_none_of.predicate_spec xs
          (fun x => Some (bool_decide (x <> 0)%Z))
          (fun _ => emp)).
  Proof. apply specify_mono; go. Qed.

  Definition symbolic_is_nonzero_predicate_spec_C :=
    [CANCEL] symbolic_is_nonzero_predicate_spec.
  #[local] Hint Resolve symbolic_is_nonzero_predicate_spec_C : br_hints.

  cpp.spec "all_nonzero_or_flag(const unsigned char*, unsigned long, bool)"
    as all_nonzero_or_flag_spec from symbolic_cpp.source with
    (\arg{bytes_p} "bytes" (Vptr bytes_p)
     \arg{count} "count" (Vint count)
     \arg{flag} "flag" (Vbool flag)
     \prepost{q xs} bytes_p |->
       array_sliceR Tuchar 0 count (fun x => ucharR q x) xs
     \require valid<"unsigned long"> count
     \post[Vint (if (forallb (fun x => bool_decide (x <> 0)%Z) xs || flag)%bool
                 then 1 else 0)] emp).

  Context {MOD : symbolic_cpp.source ⊧ σ}.

  Lemma all_nonzero_or_flag_ok :
    verify[symbolic_cpp.source] all_nonzero_or_flag_spec.
  Proof using MOD.
    verify_spec; go.
    iExists (fun x => Some (bool_decide (x <> 0)%Z)), (fun _ => emp).
    go.
    iDestruct select (match all_any_none_of.all_value _ xs with
                      | Some b => [| _ = b |]
                      | None => emp
                      end) as "Hresult".
    iEval (rewrite all_any_none_of.all_value_function) in "Hresult".
    iDestruct "Hresult" as %Hresult.
    wp_if.
    all: intros; go.
    1: iPureIntro; destruct (forallb (fun x => bool_decide (x <> 0)%Z) xs);
       simpl in *; done.
    destruct flag; go.
    all: iPureIntro; destruct (forallb (fun x => bool_decide (x <> 0)%Z) xs);
         simpl in *; done.
  Qed.

End with_cpp.
