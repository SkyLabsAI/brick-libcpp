(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.
Require Import Stdlib.Strings.String Stdlib.Strings.Byte.

(** * [std::istream >> int] on finite inputs

    [parse s] runs [istream.read_int] on the characters of [s]. The examples
    match what libstdc++ does for [std::istringstream(s) >> n]
    ([facet.num.get.virtuals], [istream.formatted.arithmetic]). *)
Fixpoint feed {T} (it : itree istream.input_char T) (cs : list N) : option T :=
  match it, cs with
  | Ret v, _ => Some v
  | Do act k, c :: cs =>
      (match act in istream.input_char U return (U -> _) -> _ with
       | istream.read => fun k => feed (k c) cs
       end) k
  | _, _ => None
  end.

Definition parse (s : String.string) : option (N * option Z) :=
  feed istream.read_int (Byte.to_N <$> String.list_byte_of_string s).

(** Values, with the delimiter that [read_int] consumed. *)
Example parse_plain : parse "12
" = Some (10%N, Some 12%Z) := eq_refl.
Example parse_ws_plus : parse "  +7 " = Some (32%N, Some 7%Z) := eq_refl.
Example parse_neg_zero : parse "-0;" = Some (59%N, Some 0%Z) := eq_refl.
Example parse_neg : parse "-35 " = Some (32%N, Some (-35)%Z) := eq_refl.
Example parse_max : parse "2147483647 " = Some (32%N, Some 2147483647%Z) := eq_refl.
Example parse_big : parse "2147483648 " = Some (32%N, Some 2147483648%Z) := eq_refl.
Example parse_small : parse "-2147483649 " = Some (32%N, Some (-2147483649)%Z) := eq_refl.
(** Conversion failures. *)
Example parse_letters : parse "abc" = Some (97%N, None) := eq_refl.
Example parse_sign_only : parse "-
" = Some (10%N, None) := eq_refl.
Example parse_two_signs : parse "+-5" = Some (45%N, None) := eq_refl.

(** What [istream_take_int_spec] lets a caller continue with, given the
    result of [read_int]. *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Ltac accept :=
    rewrite /istream.take_int_k; cbn [snd];
    iIntros "$"; iPureIntro; split; vm_compute; congruence.
  #[local] Ltac reject :=
    rewrite /istream.take_int_k; cbn [snd];
    iIntros "[% _]"; exfalso; revert select (_ <= _ <= _)%Z;
    vm_compute; intros [? ?]; congruence.

  (** Representable values, including the limits, continue. *)
  Lemma take_int_plain K : K 12%Z ⊢ istream.take_int_k K (10%N, Some 12%Z).
  Proof. accept. Qed.

  Lemma take_int_max K :
    K 2147483647%Z ⊢ istream.take_int_k K (32%N, Some 2147483647%Z).
  Proof. accept. Qed.

  Lemma take_int_min K :
    K (-2147483648)%Z ⊢ istream.take_int_k K (32%N, Some (-2147483648)%Z).
  Proof. accept. Qed.

  (** Out-of-range values and conversion failures are defined behavior: the
      stream stores the nearest [int] limit, or 0, and sets [failbit]. The spec
      does not model [failbit], so it blocks these callers, soundly. *)
  Lemma take_int_big K : istream.take_int_k K (32%N, Some 2147483648%Z) ⊢ False.
  Proof. reject. Qed.

  Lemma take_int_small K : istream.take_int_k K (32%N, Some (-2147483649)%Z) ⊢ False.
  Proof. reject. Qed.

  Lemma take_int_failure K c : istream.take_int_k K (c, None) ⊢ False.
  Proof. rewrite /istream.take_int_k; cbn [snd]. by iIntros "[]". Qed.
End with_cpp.
