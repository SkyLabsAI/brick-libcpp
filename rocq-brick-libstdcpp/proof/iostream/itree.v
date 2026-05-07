CoInductive itree {E : Type -> Type} {T : Type} : Type :=
| Ret (_ : T)
| Tau (_ : itree)
| Do {U} (_ : E U) (_ : U -> itree).
#[global] Arguments itree E T : clear implicits.

Section with_E.
  Context {E : Type -> Type}.

  CoFixpoint bind {T U} (it : itree E T) (k : T -> itree E U) : itree E U :=
    match it with
    | Ret v => k v
    | Tau it => Tau (bind it k)
    | Do e k' => Do e (fun x => bind (k' x) k)
    end.

End with_E.

Require Import stdpp.base.
Require Import skylabs.prelude.sts.

Section as_lts.
  Context {E : Type -> Type}.
  Context {Evt : Type}.

  Context {as_evt : forall {T}, E T -> T -> Evt}.

  Variant itree_step : itree E unit -> option Evt -> itree E unit -> Prop :=
    | step_do {T} {act : E T} (r : T) k
      : itree_step (Do act k) (Some $ as_evt _ act r) (k r)
    | step_tau {k}
      : itree_step (Tau k) None k.

  Definition itree_lts (it : itree E unit) : LTS Evt :=
    {| Sts._state := itree E unit
     ; Sts._init_state := eq it
     ; Sts._step := itree_step |}.
End as_lts.
