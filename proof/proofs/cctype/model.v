(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Stdlib.Strings.Byte.
Require Import skylabs.prelude.base.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

#[local]  Abbreviation ord c := (Evaluate (Z.of_N (Byte.to_N c))) (only parsing).

Definition islower (c : Z) : bool :=
  bool_decide (ord "a" <= c <= ord "z").

Definition isupper (c : Z) : bool :=
  bool_decide (ord "A" <= c <= ord "Z").

Definition isalpha (c : Z) : bool :=
  islower c || isupper c.

Definition isdigit (c : Z) : bool :=
  bool_decide (ord "0" <= c <= ord  "9").

Definition isalnum (c : Z) : bool :=
  isalpha c || isdigit c.

Definition isspace (c : Z) : bool :=
  bool_decide (c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13).

Definition isprint (c : Z) : bool :=
  bool_decide (32 <= c <= 126).

Definition iscntrl (c : Z) : bool :=
  bool_decide ((0 <= c <= 31) ∨ c = 127).

Definition isgraph (c : Z) : bool :=
  bool_decide (33 <= c <= 126).

Definition isxdigit (c : Z) : bool :=
  isdigit c || bool_decide ((ord "A" <= c <= ord "F") ∨ (ord "a" <= c <= ord "f")).

(* ispunct is printable characters minus spaces, letters, and numbers *)
Definition ispunct (c : Z) : bool :=
  isprint c && ~~isalnum c && ~~isspace c.

Definition tolower (c : Z) : Z :=
  if isupper c then c + 32 else c.

Definition toupper (c : Z) : Z :=
  if islower c then c - 32 else c.

Goal forall c, isupper c -> islower (tolower c).
Proof.
  rewrite /tolower/isupper/islower.
  intros; repeat case_bool_decide; compute; first [ assumption | lia ].
Qed.
Goal forall c, islower c -> isupper (toupper c).
Proof.
  rewrite /toupper/isupper/islower.
  intros; repeat case_bool_decide; compute; first [ assumption | lia ].
Qed.

(* Tests for isalpha *)
Succeed Example isalpha_uppercase_A : isalpha 65 = true := eq_refl.
Succeed Example isalpha_uppercase_Z : isalpha 90 = true := eq_refl.
Succeed Example isalpha_lowercase_a : isalpha 97 = true := eq_refl.
Succeed Example isalpha_lowercase_z : isalpha 122 = true := eq_refl.
Succeed Example isalpha_before_A : isalpha 64 = false := eq_refl.
Succeed Example isalpha_after_Z : isalpha 91 = false := eq_refl.
Succeed Example isalpha_before_a : isalpha 96 = false := eq_refl.
Succeed Example isalpha_after_z : isalpha 123 = false := eq_refl.
Succeed Example isalpha_digit : isalpha 48 = false := eq_refl.
Succeed Example isalpha_space : isalpha 32 = false := eq_refl.
Succeed Example isalpha_tab : isalpha 9 = false := eq_refl.
Succeed Example isalpha_negative : isalpha (-1) = false := eq_refl.
Succeed Example isalpha_extended : isalpha 128 = false := eq_refl.

(* Tests for isdigit *)
Succeed Example isdigit_0 : isdigit 48 = true := eq_refl.
Succeed Example isdigit_9 : isdigit 57 = true := eq_refl.
Succeed Example isdigit_before_0 : isdigit 47 = false := eq_refl.
Succeed Example isdigit_after_9 : isdigit 58 = false := eq_refl.
Succeed Example isdigit_letter : isdigit 65 = false := eq_refl.
Succeed Example isdigit_space : isdigit 32 = false := eq_refl.
Succeed Example isdigit_negative : isdigit (-1) = false := eq_refl.
Succeed Example isdigit_extended : isdigit 128 = false := eq_refl.

(* Tests for isalnum *)
Succeed Example isalnum_digit_0 : isalnum 48 = true := eq_refl.
Succeed Example isalnum_digit_9 : isalnum 57 = true := eq_refl.
Succeed Example isalnum_uppercase_A : isalnum 65 = true := eq_refl.
Succeed Example isalnum_uppercase_Z : isalnum 90 = true := eq_refl.
Succeed Example isalnum_lowercase_a : isalnum 97 = true := eq_refl.
Succeed Example isalnum_lowercase_z : isalnum 122 = true := eq_refl.
Succeed Example isalnum_before_0 : isalnum 47 = false := eq_refl.
Succeed Example isalnum_after_9 : isalnum 58 = false := eq_refl.
Succeed Example isalnum_before_A : isalnum 64 = false := eq_refl.
Succeed Example isalnum_after_Z : isalnum 91 = false := eq_refl.
Succeed Example isalnum_before_a : isalnum 96 = false := eq_refl.
Succeed Example isalnum_after_z : isalnum 123 = false := eq_refl.
Succeed Example isalnum_space : isalnum 32 = false := eq_refl.
Succeed Example isalnum_negative : isalnum (-1) = false := eq_refl.

(* Tests for isspace *)
Succeed Example isspace_space : isspace 32 = true := eq_refl.
Succeed Example isspace_tab : isspace 9 = true := eq_refl.
Succeed Example isspace_newline : isspace 10 = true := eq_refl.
Succeed Example isspace_vtab : isspace 11 = true := eq_refl.
Succeed Example isspace_formfeed : isspace 12 = true := eq_refl.
Succeed Example isspace_carriage : isspace 13 = true := eq_refl.
Succeed Example isspace_letter : isspace 65 = false := eq_refl.
Succeed Example isspace_digit : isspace 48 = false := eq_refl.
Succeed Example isspace_before_tab : isspace 8 = false := eq_refl.
Succeed Example isspace_after_cr : isspace 14 = false := eq_refl.
Succeed Example isspace_negative : isspace (-1) = false := eq_refl.

(* Tests for islower *)
Succeed Example islower_a : islower 97 = true := eq_refl.
Succeed Example islower_z : islower 122 = true := eq_refl.
Succeed Example islower_before_a : islower 96 = false := eq_refl.
Succeed Example islower_after_z : islower 123 = false := eq_refl.
Succeed Example islower_uppercase : islower 65 = false := eq_refl.
Succeed Example islower_digit : islower 48 = false := eq_refl.
Succeed Example islower_space : islower 32 = false := eq_refl.
Succeed Example islower_negative : islower (-1) = false := eq_refl.

(* Tests for isupper *)
Succeed Example isupper_A : isupper 65 = true := eq_refl.
Succeed Example isupper_Z : isupper 90 = true := eq_refl.
Succeed Example isupper_before_A : isupper 64 = false := eq_refl.
Succeed Example isupper_after_Z : isupper 91 = false := eq_refl.
Succeed Example isupper_lowercase : isupper 97 = false := eq_refl.
Succeed Example isupper_digit : isupper 48 = false := eq_refl.
Succeed Example isupper_space : isupper 32 = false := eq_refl.
Succeed Example isupper_negative : isupper (-1) = false := eq_refl.

(* Tests for isprint *)
Succeed Example isprint_space : isprint 32 = true := eq_refl.
Succeed Example isprint_tilde : isprint 126 = true := eq_refl.
Succeed Example isprint_letter_A : isprint 65 = true := eq_refl.
Succeed Example isprint_letter_z : isprint 122 = true := eq_refl.
Succeed Example isprint_digit : isprint 48 = true := eq_refl.
Succeed Example isprint_symbol : isprint 33 = true := eq_refl.
Succeed Example isprint_before_space : isprint 31 = false := eq_refl.
Succeed Example isprint_after_tilde : isprint 127 = false := eq_refl.
Succeed Example isprint_null : isprint 0 = false := eq_refl.
Succeed Example isprint_tab : isprint 9 = false := eq_refl.
Succeed Example isprint_newline : isprint 10 = false := eq_refl.
Succeed Example isprint_negative : isprint (-1) = false := eq_refl.

(* Tests for ispunct *)
Succeed Example ispunct_period : ispunct 46 = true := eq_refl.  (* . *)
Succeed Example ispunct_comma : ispunct 44 = true := eq_refl.   (* , *)
Succeed Example ispunct_exclamation : ispunct 33 = true := eq_refl. (* ! *)
Succeed Example ispunct_semicolon : ispunct 59 = true := eq_refl. (* ; *)
Succeed Example ispunct_colon : ispunct 58 = true := eq_refl.    (* : *)
Succeed Example ispunct_question : ispunct 63 = true := eq_refl. (* ? *)
Succeed Example ispunct_minus : ispunct 45 = true := eq_refl.    (* - *)
Succeed Example ispunct_letter : ispunct 65 = false := eq_refl.
Succeed Example ispunct_digit : ispunct 48 = false := eq_refl.
Succeed Example ispunct_space : ispunct 32 = false := eq_refl.
Succeed Example ispunct_tab : ispunct 9 = false := eq_refl.
Succeed Example ispunct_newline : ispunct 10 = false := eq_refl.
Succeed Example ispunct_negative : ispunct (-1) = false := eq_refl.

(* Tests for iscntrl *)
Succeed Example iscntrl_null : iscntrl 0 = true := eq_refl.
Succeed Example iscntrl_bell : iscntrl 7 = true := eq_refl.
Succeed Example iscntrl_backspace : iscntrl 8 = true := eq_refl.
Succeed Example iscntrl_tab : iscntrl 9 = true := eq_refl.
Succeed Example iscntrl_newline : iscntrl 10 = true := eq_refl.
Succeed Example iscntrl_vtab : iscntrl 11 = true := eq_refl.
Succeed Example iscntrl_formfeed : iscntrl 12 = true := eq_refl.
Succeed Example iscntrl_carriage : iscntrl 13 = true := eq_refl.
Succeed Example iscntrl_last_before_space : iscntrl 31 = true := eq_refl.
Succeed Example iscntrl_delete : iscntrl 127 = true := eq_refl.
Succeed Example iscntrl_space : iscntrl 32 = false := eq_refl.
Succeed Example iscntrl_letter : iscntrl 65 = false := eq_refl.
Succeed Example iscntrl_tilde : iscntrl 126 = false := eq_refl.
Succeed Example iscntrl_extended : iscntrl 128 = false := eq_refl.
Succeed Example iscntrl_negative : iscntrl (-1) = false := eq_refl.

(* Tests for isgraph *)
Succeed Example isgraph_exclamation : isgraph 33 = true := eq_refl. (* First graphical *)
Succeed Example isgraph_tilde : isgraph 126 = true := eq_refl.      (* Last graphical *)
Succeed Example isgraph_letter_A : isgraph 65 = true := eq_refl.
Succeed Example isgraph_letter_z : isgraph 122 = true := eq_refl.
Succeed Example isgraph_digit : isgraph 48 = true := eq_refl.
Succeed Example isgraph_symbol : isgraph 35 = true := eq_refl.      (* # *)
Succeed Example isgraph_space : isgraph 32 = false := eq_refl.
Succeed Example isgraph_before_exclamation : isgraph 32 = false := eq_refl.
Succeed Example isgraph_after_tilde : isgraph 127 = false := eq_refl.
Succeed Example isgraph_tab : isgraph 9 = false := eq_refl.
Succeed Example isgraph_newline : isgraph 10 = false := eq_refl.
Succeed Example isgraph_negative : isgraph (-1) = false := eq_refl.

(* Tests for isxdigit *)
Succeed Example isxdigit_0 : isxdigit 48 = true := eq_refl.
Succeed Example isxdigit_9 : isxdigit 57 = true := eq_refl.
Succeed Example isxdigit_A : isxdigit 65 = true := eq_refl.
Succeed Example isxdigit_F : isxdigit 70 = true := eq_refl.
Succeed Example isxdigit_a : isxdigit 97 = true := eq_refl.
Succeed Example isxdigit_f : isxdigit 102 = true := eq_refl.
Succeed Example isxdigit_before_0 : isxdigit 47 = false := eq_refl.
Succeed Example isxdigit_after_9 : isxdigit 58 = false := eq_refl.
Succeed Example isxdigit_before_A : isxdigit 64 = false := eq_refl.
Succeed Example isxdigit_after_F : isxdigit 71 = false := eq_refl.
Succeed Example isxdigit_before_a : isxdigit 96 = false := eq_refl.
Succeed Example isxdigit_after_f : isxdigit 103 = false := eq_refl.
Succeed Example isxdigit_g : isxdigit 103 = false := eq_refl.
Succeed Example isxdigit_G : isxdigit 71 = false := eq_refl.
Succeed Example isxdigit_space : isxdigit 32 = false := eq_refl.
Succeed Example isxdigit_negative : isxdigit (-1) = false := eq_refl.

(* Tests for tolower *)
Succeed Example tolower_A : tolower 65 = 97 := eq_refl.  (* A -> a *)
Succeed Example tolower_Z : tolower 90 = 122 := eq_refl. (* Z -> z *)
Succeed Example tolower_a : tolower 97 = 97 := eq_refl.  (* Already lowercase *)
Succeed Example tolower_z : tolower 122 = 122 := eq_refl. (* Already lowercase *)
Succeed Example tolower_before_A : tolower 64 = 64 := eq_refl.
Succeed Example tolower_after_Z : tolower 91 = 91 := eq_refl.
Succeed Example tolower_digit : tolower 48 = 48 := eq_refl.
Succeed Example tolower_space : tolower 32 = 32 := eq_refl.
Succeed Example tolower_punct : tolower 46 = 46 := eq_refl.
Succeed Example tolower_negative : tolower (-1) = (-1) := eq_refl.
Succeed Example tolower_extended : tolower 128 = 128 := eq_refl.

(* Tests for toupper *)
Succeed Example toupper_a : toupper 97 = 65 := eq_refl.  (* a -> A *)
Succeed Example toupper_z : toupper 122 = 90 := eq_refl. (* z -> Z *)
Succeed Example toupper_A : toupper 65 = 65 := eq_refl.  (* Already uppercase *)
Succeed Example toupper_Z : toupper 90 = 90 := eq_refl.  (* Already uppercase *)
Succeed Example toupper_before_a : toupper 96 = 96 := eq_refl.
Succeed Example toupper_after_z : toupper 123 = 123 := eq_refl.
Succeed Example toupper_digit : toupper 48 = 48 := eq_refl.
Succeed Example toupper_space : toupper 32 = 32 := eq_refl.
Succeed Example toupper_punct : toupper 46 = 46 := eq_refl.
Succeed Example toupper_negative : toupper (-1) = (-1) := eq_refl.
Succeed Example toupper_extended : toupper 128 = 128 := eq_refl.
