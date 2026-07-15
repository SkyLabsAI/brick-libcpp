
(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.specs.

Require Export skylabs.brick.libstdcpp.cwctype.pred.
Require Import skylabs.brick.libstdcpp.cwctype.inc_cwctype_cpp.

#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  (** The classifiers expose only the portable zero/nonzero result convention. *)
  cpp.spec (named "iswalnum") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswalnum wc) |]).

  cpp.spec (named "iswalpha") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswalpha wc) |]).

  cpp.spec (named "iswblank") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswblank wc) |]).

  cpp.spec (named "iswcntrl") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswcntrl wc) |]).

  cpp.spec (named "iswdigit") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswdigit wc) |]).

  cpp.spec (named "iswgraph") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswgraph wc) |]).

  cpp.spec (named "iswlower") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswlower wc) |]).

  cpp.spec (named "iswprint") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswprint wc) |]).

  cpp.spec (named "iswpunct") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswpunct wc) |]).

  cpp.spec (named "iswspace") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswspace wc) |]).

  cpp.spec (named "iswupper") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswupper wc) |]).

  cpp.spec (named "iswxdigit") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post{result}[Vint result]
       [| classifier_result result (iswxdigit wc) |]).

  (** Case conversion returns the exact C-locale model value. *)
  cpp.spec (named "towlower") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post[Vint (towlower wc)] emp).

  cpp.spec (named "towupper") with
    (\arg{wc} "__wc" (Vint wc)
     \require valid_wint wc
     \post[Vint (towupper wc)] emp).
End with_cpp.
Require Import skylabs.auto.core.hints.

(** Pure consequences used by client assertions.  These helpers preserve the
    standard's freedom to choose any nonzero result for a true classifier. *)
Lemma classifier_result_false_zero result :
  bool_decide (result <> 0) = false -> result = 0.
Proof.
  intros Hresult. case_bool_decide; first discriminate. lia.
Qed.

Lemma classifier_result_true_nonzero result :
  bool_decide (result <> 0) = true -> result <> 0.
Proof.
  intros Hresult. case_bool_decide; first assumption. discriminate.
Qed.

Lemma valid_wint_of_wchar c :
  SolveArith (0 <= c <= 2147483647) ->
  c = cwctype_weof \/ (0 <= c <= 2147483647)%Z.
Proof. destruct 1. right. Arith.arith_solve. Qed.

Lemma valid_wint_of_weof c :
  c = cwctype_weof ->
  c = cwctype_weof \/ (0 <= c <= 2147483647)%Z.
Proof. auto. Qed.

#[global] Hint Resolve
  classifier_result_false_zero classifier_result_true_nonzero
  valid_wint_of_wchar valid_wint_of_weof : pure.


