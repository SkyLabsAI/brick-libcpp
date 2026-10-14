Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.

#[local] Set Primitive Projections.

(** The fundamental object types for which an <<alignof>> expression is valid.
    <<void>> is fundamental, but is not an object type. *)
Definition is_fundamental_alignment_type (ty : type) : Prop :=
  match drop_qualifiers ty with
  | Tnum _ _ | Tchar_ _ | Tfloat_ _ | Tbool | Tnullptr => True
  | _ => False
  end.

Definition fundamental_alignment {σ : genv} (al : N) : Prop :=
  exists ty : type,
    is_fundamental_alignment_type ty /\ align_of ty = Some al.

(** Implementation-defined alignment support, as in [basic.align]/4.
    The additional set may be empty, and need not be exhausted by the types
    declared in the current environment. Its members must be powers of two.

    An implementation supplies this model together with its allocation specs.
    Every defined type alignment must be included in its valid alignment set;
    this does not constrain a raw allocation to any particular object type. *)
Class allocation_alignment_support (σ : genv) := {
  additional_alignments : N -> Prop;
  additional_alignments_power_of_two : forall al : N,
    additional_alignments al -> exists n : N, al = N.pow 2 n;
  type_alignment_supported : forall (ty : type) (al : N),
    @align_of σ ty = Some al ->
    @fundamental_alignment σ al \/ additional_alignments al;
}.

#[global] Arguments allocation_alignment_support σ : clear implicits.
#[global] Arguments additional_alignments {_ _} _.
#[global] Arguments additional_alignments_power_of_two {_ _} _ _.
#[global] Arguments type_alignment_supported {_ _} _ _ _.

Definition supported_alignment {σ : genv}
    `{alignment_support : !allocation_alignment_support σ} (al : N) : Prop :=
  fundamental_alignment al \/ additional_alignments al.

Section with_alignment_support.
  Context {σ : genv} `{alignment_support : !allocation_alignment_support σ}.

  Lemma supported_alignment_of_type (ty : type) (al : N) :
    align_of ty = Some al -> supported_alignment al.
  Proof. apply type_alignment_supported. Qed.

  Lemma supported_alignment_additional (al : N) :
    additional_alignments al -> supported_alignment al.
  Proof. intros H; right; exact H. Qed.

  Lemma supported_alignment_power_of_two (al : N) :
    supported_alignment al -> exists n : N, al = N.pow 2 n.
  Proof.
    intros [[ty [_ Hty]] | Hadditional].
    - eapply align_of_power_of_two; exact Hty.
    - apply additional_alignments_power_of_two; exact Hadditional.
  Qed.
End with_alignment_support.
