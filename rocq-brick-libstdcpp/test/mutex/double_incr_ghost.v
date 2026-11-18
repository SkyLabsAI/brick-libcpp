Require Import skylabs.auto.cpp.prelude.proof.
Require Import iris.algebra.lib.frac_auth.

(** Each worker receives half of a permission to enter the critical section.
    The first worker deposits its half and returns the exclusive authority;
    the second gathers both halves and transfers ownership of the counter.
    Only the counter's parity is tracked. Joining both workers recovers its
    ownership because they cannot both return the exclusive authority. *)
Module double_incr_protocol.
  Canonical Structure completionR : cmra := frac_authR unitUR.

  Class G `{Σ : cpp_logic} := {
    #[local] completion_own :: HasOwn (iPropI _Σ) completionR;
    #[local] completion_upd :: HasOwnUpd (iPropI _Σ) completionR;
    #[local] completion_valid :: HasOwnValid (iPropI _Σ) completionR;
  }.
  #[global] Arguments G {_ _} Σ : assert.

  Definition gname := iprop.gname.

  Lemma trim_add_two_even (n : Z) :
    (n mod 2 = 0)%Z -> (trim 32 (n + 2) mod 2 = 0)%Z.
  Proof.
    intros Hn. rewrite /trim Z.mod_mod_divide.
    - rewrite Z.add_mod; last lia. rewrite Hn. reflexivity.
    - exists (2 ^ 31)%Z. reflexivity.
  Qed.

  Section proof.
    Context `{Σ : cpp_logic, σ : genv, !G Σ}.

    Definition auth (γ : iprop.gname) : mpred :=
      own γ ((●F ()) : completionR).
    Definition frac (γ : iprop.gname) (q : Qp) : mpred :=
      own γ ((◯F{q} ()) : completionR).

    Definition evenR (x : ptr) : mpred :=
      ∃ n : Z, x |-> uintR 1$m n ** [| (n mod 2 = 0)%Z |].

    Definition protected (γ : gname) (x : ptr) : mpred :=
      (auth γ ** evenR x) ∨
      (frac γ (1 / 2) ** evenR x) ∨ frac γ 1.

    Definition done (γ : gname) (x : ptr) : mpred :=
      auth γ ∨ evenR x.

    Lemma alloc (x : ptr) :
      evenR x |-- (|==> ∃ γ,
        protected γ x ** frac γ (1 / 2) ** frac γ (1 / 2)).
    Proof.
      iIntros "Hx".
      iMod (own_alloc (((●F ()) ⋅ (◯F ())) : completionR))
        as (γ) "[Ha Hf]"; first (apply frac_auth_valid; done).
      have Hsplit : ((◯F ()) : completionR) ≡
          ((◯F{1 / 2} ()) ⋅ (◯F{1 / 2} ())).
      { rewrite -frac_auth_frag_op Qp.half_half. done. }
      iEval (rewrite Hsplit own_op) in "Hf".
      iModIntro. iExists γ. rewrite /frac. iFrame "Hf".
      rewrite /protected. iLeft. iFrame.
    Qed.

    (** After the physical increments, the first worker deposits its half and
        the second gathers both halves. The completed invariant keeps the full
        fraction, preventing another worker from presenting an unused half. *)
    Lemma prepare γ (x : ptr) :
      protected γ x ** frac γ (1 / 2) |--
        evenR x ** (evenR x -* protected γ x ** done γ x).
    Proof.
      rewrite /protected /done /auth /frac.
      iIntros "[[H | [H | H]] Hf]".
      - iDestruct "H" as "[Ha Hx]". iFrame "Hx". iIntros "Hx".
        iSplitL "Hf Hx".
        + iRight. iLeft. iFrame.
        + iLeft. done.
      - iDestruct "H" as "[Hstored Hx]". iFrame "Hx". iIntros "Hx".
        iCombine "Hstored Hf" as "Hfull".
        iSplitL "Hfull".
        + iRight. iRight. done.
        + iRight. done.
      - iDestruct (own_valid_2 with "H Hf") as %Hv.
        move: Hv. rewrite -frac_auth_frag_op frac_auth_frag_valid.
        move=> [Hfrac _]. exfalso. compute in Hfrac. done.
    Qed.

    Lemma join γ (x : ptr) : done γ x ** done γ x |-- evenR x.
    Proof.
      rewrite /done. iIntros "[[H1 | H1] [H2 | H2]]"; try iAssumption.
      rewrite /auth.
      iDestruct (own_valid_2 with "H1 H2") as %Hv.
      move: Hv. rewrite auth_auth_op_valid. done.
    Qed.
  End proof.
End double_incr_protocol.
