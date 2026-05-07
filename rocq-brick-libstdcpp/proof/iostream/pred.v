(**
Tentative iostreams specs.

These are trace-based specifications, and there is a _wish_ to move to a
different style of specifications.

*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.

Require Import skylabs.auto.hints.kont.

Require Import skylabs.brick.libstdcpp.iostream.itree.

Require Import skylabs.brick.libstdcpp.iostream.inc_iostream_cpp.

(** TODO upstream START *)
#[only(cfracsplittable)] derive cstring.R.

(** TODO upstream *)
#[global] Bind Scope bs_scope with cstring.t.
(* We only have `Bind Scope bs_scope with t.` inside `Module cstring.` *)
(** TODO upstream END *)

(** A handler for events as a predicate transformer.

    Generally, this will be an <AU> that proves that <evt> is a valid next event.
 *)
Class SepHandler (PROP : bi) (evt : Type) : Type :=
{ do : propset evt -> (evt -> PROP) -> PROP
  (** This is effectively an <<AU>> that performs the event and then continues *)
; do_frame : forall evtP, ProperFrame (T:=[tele (_ : evt)]) (do evtP)
; do_ne : forall n, Proper ((≡) ==> pointwise_relation _ (dist n) ==> (dist n)) do
}.
#[global] Hint Opaque do : sl_opacity.

(* TODO: these should be replaced by library definitions *)
Section interp_itree.
  Context {PROP : bi}.
  Context {PROP_LATER : BiLaterContractive PROP}.

  Context {E : Type -> Type}.
  Context {Evt : Type}.
  Variable as_evt : forall {T}, E T -> T -> Evt.

  Context (SH : SepHandler PROP Evt).

  #[local]
  Definition interp_do_body {T} (K : T -> PROP) (rec : itree E T -d> PROP) : itree E T -d> PROP :=
    funI it =>
    match it with
    | Ret v => K v
    | Tau x => |> rec x
    | Do act k =>
        letI* evt := do {[ evt | exists r, evt = as_evt act r ]} in
        ∃ r, [| evt = as_evt act r |] ∗ |> rec (k r)
    end.

  #[local]
  Instance interp_do_body_contractive {T} {K : T -> PROP} : Contractive (interp_do_body K).
  Proof using PROP_LATER.
    repeat intro.
    destruct x0; simpl; try eauto.
    { apply later_contractive. constructor.
      intros. apply H. done. }
    { eapply do_ne. done.
      intro. apply bi.exist_ne; intro. apply bi.sep_ne. done. apply later_contractive.
      constructor; intros; apply H; done. }
  Qed.

  Definition interp_itree {T} (it : itree E T) (K : T -> PROP) : PROP :=
    fixpoint (A:=_ -d> PROP) (interp_do_body K) it.

End interp_itree.
#[global] Arguments interp_itree {PROP _ E Event} as_evt {SepHandler _} it _%_I : rename.


(** Events that send output.

    For most buffered streams, writes go to the buffer and are only guaranteed
    to be sent to the consumer on a [Flush].
 *)
Variant output_event : Set :=
  | Write (_ : N).

Variant input_event : Set :=
  | Read (_ : N).

(** The behavior of an [ostream] is described by a handler of an [output_event]  *)
Notation Ostream := (SepHandler mpred output_event).
Notation Istream := (SepHandler mpred input_event).

Module ostream.
  Parameter gname : Set.

  (** TODO: Add support for <iomanip> *)
  Parameter R : forall `{Σ : cpp_logic} {σ : genv}, Ostream -> gname -> cQp.t -> Rep.
  #[only(cfracsplittable)] derive R.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    #[global] Instance: Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

  End with_cpp.
End ostream.

Module istream.
  Parameter gname : Set.
  Parameter R : forall `{Σ : cpp_logic} {σ : genv}, Istream -> gname -> cQp.t -> Rep.
  #[only(cfracsplittable)] derive R.

  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    #[global] Instance: Cbn (Learn (learn_eq ==> learn_eq ==> any ==> learn_hints.fin) R).
    Proof. solve_learnable. Qed.

  End with_cpp.

End istream.
