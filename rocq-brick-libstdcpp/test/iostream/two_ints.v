(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.iostream.spec.

(** * Two consecutive [int] extractions

    On the input "12-34 ", [second] returns -34 with libstdc++: the first
    extraction stops at '-' and leaves it in the stream.

    UNSOUND: [istream_take_int_spec] consumes the '-', so [second_ok] proves
    that [second] returns 34. *)
cpp.prog source flags "-std=c++20 -stdlib=libstdc++" prog cpp:{{
  #include <istream>
  int second(std::istream &in) {
    int a = 0, b = 0;
    in >> a;
    in >> b;
    return b;
  }
}}.

(** A stream that delivers the characters of a fixed input, one per read.
    [remaining cs] owns the characters [cs] not read yet. *)
Section script.
  Context `{Σ : cpp_logic} (remaining : list N -> mpred).

  #[program]
  Definition script : Istream :=
    {| do evts K := ∃ c cs, remaining (c :: cs) ** [| Read c ∈ evts |] **
                     (remaining cs -∗ K (Read c)) |}%I.
  Next Obligation.
    intros evts. constructor => K K'. iIntros "HK (%c & %cs & R & % & W)".
    iExists c, cs. iFrame "R %". iIntros "R".
    iApply ("HK" $! ([tele_arg (Read c)] : tele_arg [tele (_ : input_event)])). by iApply "W".
  Qed.
  Next Obligation. solve_proper. Qed.

  Lemma interp_unfold {T} (it : itree istream.input_char T) K :
    interp_itree istream.as_event script it K ⊣⊢
    match it with
    | Ret v => K v
    | Tau x => ▷ interp_itree istream.as_event script x K
    | Do act k =>
        script.(do) {[ evt | (∃ r, evt = istream.as_event _ act r)%type ]}
          (λ evt : input_event, (∃ r, [| evt = istream.as_event _ act r |] ∗
             ▷ interp_itree istream.as_event script (k r) K)%I : mpred)
    end.
  Proof.
    rewrite /interp_itree.
    rewrite (fixpoint_unfold (A:=_ -d> mpred)
      (itree_prop.interp_do_body istream.as_event script K) it).
    by destruct it.
  Qed.
End script.

Definition chars (s : String.string) : list N :=
  Byte.to_N <$> String.list_byte_of_string s.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv} (remaining : list N -> mpred).

  cpp.spec "second(std::istream&)" from source as second_spec with (
    \arg{inp} "in" (Vref inp)
    \pre{g} inp |-> istream.R (script remaining) g 1$m
    \pre remaining (chars "12-34 ")
    \post{n}[Vint n] [| n = 34 |]%Z **
      ∃ g' cs, inp |-> istream.R (script remaining) g' 1$m ** remaining cs).

  (** One read from [script], of the character [c] at the head of the input. *)
  #[local] Ltac read_char :=
    rewrite interp_unfold; cbn -[interp_itree]; iExists _, _; iFrame "R";
    iSplitR; [iPureIntro; rewrite elem_of_PropSet; eauto|];
    iIntros "R"; iExists _; iSplitR; [iPureIntro; reflexivity|]; iNext.
  #[local] Ltac finish :=
    rewrite interp_unfold; cbn -[interp_itree]; iFrame "R"; iPureIntro;
    split; [split; vm_compute; congruence|vm_compute; reflexivity].

  (** The first extraction reads "12-", the second "34 ". *)
  Lemma read_12 :
    remaining (chars "12-34 ") ⊢
    interp_itree istream.as_event (script remaining) istream.read_int
      (istream.take_int_k (λ n, [| n = 12%Z |] ∗ remaining (chars "34 "))).
  Proof. iIntros "R". do 3 read_char. finish. Qed.

  Lemma read_34 :
    remaining (chars "34 ") ⊢
    interp_itree istream.as_event (script remaining) istream.read_int
      (istream.take_int_k (λ n, [| n = 34%Z |] ∗ remaining [])).
  Proof. iIntros "R". do 3 read_char. finish. Qed.

  #[local] Hint Opaque interp_itree : sl_opacity.

  Lemma second_ok : verify[source] second_spec.
  Proof.
    verify_spec. go.
    iDestruct select (remaining _) as "R".
    iExists _. iSplitL "R"; [by iApply read_12|]. go.
    iDestruct select (remaining _) as "R".
    iExists _. iSplitL "R"; [by iApply read_34|]. go.
    iDestruct select (remaining _) as "R". by iExists _.
  Qed.
End with_cpp.
