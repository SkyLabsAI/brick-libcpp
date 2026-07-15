

(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Stdlib Require Import ZArith Bool.
Require Import skylabs.prelude.base.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.

(** The target libstdc++ header's [WEOF] encoding. *)
Definition cwctype_weof : Z := 4294967295.

(** Values of the target unsigned [wint_t] that are representable as its
    signed 32-bit [wchar_t]. *)

#[global] Abbreviation valid_wchar wc := ((0 <= wc <= 2147483647)%Z) (only parsing).


(** The standard-defined input domain for the selected operations. *)

#[global] Abbreviation valid_wint wc := (wc = cwctype_weof \/ valid_wchar wc) (only parsing).

#[global] Abbreviation classifier_result result class := (bool_decide (result <> 0) = class) (only parsing).


(** Relate a C classifier's otherwise-unspecified integer result to a class. *)





Definition between (lo hi code : Z) : bool := (lo <=? code) && (code <=? hi).


Definition iswupper (code : Z) : bool := between 65 90 code.
Definition iswlower (code : Z) : bool := between 97 122 code.
Definition iswalpha (code : Z) : bool := iswupper code || iswlower code.
Definition iswdigit (code : Z) : bool := between 48 57 code.
Definition iswalnum (code : Z) : bool := iswalpha code || iswdigit code.
Definition iswxdigit (code : Z) : bool :=
  iswdigit code || between 65 70 code || between 97 102 code.

Definition iswblank (code : Z) : bool := (code =? 9) || (code =? 32).


Definition iswspace (code : Z) : bool := (code =? 9) || (code =? 10) || (code =? 11) || (code =? 12) || (code =? 13) || (code =? 32).


Definition iswcntrl (code : Z) : bool := between 0 31 code || (code =? 127).

Definition iswprint (code : Z) : bool := between 32 126 code.

Definition iswgraph (code : Z) : bool := between 33 126 code.

Definition iswpunct (code : Z) : bool :=
  iswgraph code && negb (iswalnum code).

Definition towlower (code : Z) : Z :=
  if iswupper code then code + 32 else code.
Definition towupper (code : Z) : Z :=
  if iswlower code then code - 32 else code.

(** One canonical witness among the permitted nonzero classifier results. *)
Definition canonical_classifier_result (class : bool) : Z :=
  if class then 1 else 0.

Definition iswalnum_result code := canonical_classifier_result (iswalnum code).
Definition iswalpha_result code := canonical_classifier_result (iswalpha code).
Definition iswblank_result code := canonical_classifier_result (iswblank code).
Definition iswcntrl_result code := canonical_classifier_result (iswcntrl code).
Definition iswdigit_result code := canonical_classifier_result (iswdigit code).
Definition iswgraph_result code := canonical_classifier_result (iswgraph code).
Definition iswlower_result code := canonical_classifier_result (iswlower code).
Definition iswprint_result code := canonical_classifier_result (iswprint code).
Definition iswpunct_result code := canonical_classifier_result (iswpunct code).
Definition iswspace_result code := canonical_classifier_result (iswspace code).
Definition iswupper_result code := canonical_classifier_result (iswupper code).
Definition iswxdigit_result code := canonical_classifier_result (iswxdigit code).

