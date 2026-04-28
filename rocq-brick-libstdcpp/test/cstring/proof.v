(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.hints.anyR.
(** BEGIN: SKYLABS DEFAULT PROOF IMPORTS *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.cpp.array.
Import expr_join.
#[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
#[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.
(** END: SKYLABS DEFAULT PROOF IMPORTS *)
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Import skylabs.brick.libstdcpp.test.cstring.test_cpp.

Import normalize.only_provable_norm.

Import normalize.normalize_ptr.
Import refine_lib.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : module ⊧ σ}.

  cpp.spec "test_strlen()" default.
  Lemma test_strlen_ok : verify[module] "test_strlen()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcmp()" default.
  Lemma test_strcmp_ok : verify[module] "test_strcmp()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strncmp()" default.
  Lemma test_strncmp_ok : verify[module] "test_strncmp()".
  Proof. verify_spec; go; ego. Qed.

  #[local] Fixpoint split_bytes_at_null (bytes : list N) :
      option (list N * list N) :=
    match bytes with
    | nil => None
    | 0%N :: tail => Some (nil, tail)
    | b :: rest =>
        match split_bytes_at_null rest with
        | Some (prefix, tail) => Some (b :: prefix, tail)
        | None => None
        end
    end.

  #[local] Lemma split_bytes_at_null_sound bytes prefix tail :
    split_bytes_at_null bytes = Some (prefix, tail) ->
    bytes = prefix ++ 0%N :: tail /\
    List.Forall (fun b => b <> 0%N) prefix.
  Proof.
    revert prefix tail.
    induction bytes as [|b bytes IH]; intros prefix tail Hsplit; [done|].
    destruct b as [|p].
    - simpl in Hsplit. inversion Hsplit; subst.
      split; [reflexivity|constructor].
    - simpl in Hsplit.
      destruct (split_bytes_at_null bytes) as [[prefix' tail']|] eqn:Hrec;
        [|done].
      inversion Hsplit; subst prefix tail. clear Hsplit.
      specialize (IH _ _ eq_refl) as [Hbytes Hfor].
      split.
      + simpl. rewrite Hbytes. reflexivity.
      + constructor; [discriminate|exact Hfor].
  Qed.

  #[local] Lemma split_bytes_at_null_complete prefix tail :
    List.Forall (fun b => b <> 0%N) prefix ->
    split_bytes_at_null (prefix ++ 0%N :: tail) = Some (prefix, tail).
  Proof.
    induction prefix as [|b prefix IH]; intros Hfor.
    - reflexivity.
    - inversion Hfor as [|? ? Hb Hfor']; subst.
      destruct b as [|p]; [done|].
      simpl.
      rewrite (IH Hfor').
      reflexivity.
  Qed.

  #[local] Definition split_bytes_at_cstring (bytes : list N) :
      option (list N * list N) :=
    match split_bytes_at_null bytes with
    | Some (prefix, tail) => Some (prefix ++ [0%N], tail)
    | None => None
    end.

  #[local] Lemma split_bytes_at_cstring_sound bytes zs tail :
    split_bytes_at_cstring bytes = Some (zs, tail) ->
    bytes = zs ++ tail /\
    exists prefix,
      zs = prefix ++ [0%N] /\
      List.Forall (fun b => b <> 0%N) prefix.
  Proof.
    rewrite /split_bytes_at_cstring.
    destruct (split_bytes_at_null bytes) as [[prefix tail']|] eqn:Hsplit;
      [|done].
    intros Hcstring.
    inversion Hcstring; subst zs tail. clear Hcstring.
    pose proof (split_bytes_at_null_sound _ _ _ Hsplit) as [-> Hfor].
    split.
    - change (prefix ++ 0%N :: tail' = (prefix ++ 0%N :: nil) ++ tail').
      rewrite <- app_assoc.
      reflexivity.
    - eexists. split.
      + reflexivity.
      + exact Hfor.
  Qed.

  #[local] Lemma split_bytes_at_cstring_complete prefix tail :
    List.Forall (fun b => b <> 0%N) prefix ->
    split_bytes_at_cstring (prefix ++ [0%N] ++ tail) =
      Some (prefix ++ [0%N], tail).
  Proof.
    intros Hfor.
    rewrite /split_bytes_at_cstring.
    rewrite (split_bytes_at_null_complete prefix tail Hfor).
    reflexivity.
  Qed.

  (*
  Dead lemmas
  #[local] Lemma split_bytes_at_null_spec bytes prefix tail :
    split_bytes_at_null bytes = Some (prefix, tail) <->
    bytes = prefix ++ 0%N :: tail /\
    List.Forall (fun b => b <> 0%N) prefix.
  Proof.
    split.
    - apply split_bytes_at_null_sound.
    - intros [-> Hfor].
      exact (split_bytes_at_null_complete _ _ Hfor).
  Qed.
  #[local] Lemma split_bytes_at_cstring_spec bytes zs tail :
    split_bytes_at_cstring bytes = Some (zs, tail) <->
    bytes = zs ++ tail /\
    exists prefix,
      zs = prefix ++ [0%N] /\
      List.Forall (fun b => b <> 0%N) prefix.
  Proof.
    split.
    - apply split_bytes_at_cstring_sound.
    - intros [Hbytes [prefix [Hzs Hfor]]].
      subst zs bytes.
      rewrite <- app_assoc.
      exact (split_bytes_at_cstring_complete _ _ Hfor).
  Qed.
  *)

  #[local] Fixpoint pack (zs : list N) : option cstring.t :=
    match zs with
    | nil => None
    | 0%N :: nil => Some BS.EmptyString
    | 0%N :: _ => None
    | b :: rest =>
        match Byte.of_N b, pack rest with
        | Some ch, Some s => Some (BS.String ch s)
        | _, _ => None
        end
    end.

  #[local] Lemma pack_sound zs s :
    pack zs = Some s ->
    cstring.to_zstring s = zs.
  Proof.
    revert s.
    induction zs as [|b zs IH]; intros s Hpack; [done|].
    destruct b as [|p].
    - destruct zs as [|b zs].
      + simpl in Hpack. inversion Hpack; subst s.
        rewrite cstring.to_zstring_unfold.
        reflexivity.
      + done.
    - destruct (Byte.of_N (N.pos p)) as [ch|] eqn:Hbyte.
      + destruct (pack zs) as [s'|] eqn:Hpack'.
        * rewrite /pack Hbyte /= in Hpack.
          fold pack in Hpack.
          rewrite Hpack' in Hpack.
          injection Hpack as <-.
          pose proof (IH s' eq_refl) as Hzs.
          rewrite cstring.to_zstring_unfold.
          rewrite cstring.to_zstring_unfold in Hzs.
          simpl.
          rewrite Hzs.
          assert (Hto : Byte.to_N ch = N.pos p).
          { apply Byte.to_of_N. exact Hbyte. }
          pose proof (Byte.to_N_bounded ch) as Hbound_le.
          assert (Hbound : (Byte.to_N ch < 256)%N) by lia.
          rewrite Ascii.ascii_of_byte_via_N.
          rewrite (Ascii.N_ascii_embedding _ Hbound).
          rewrite Hto.
          reflexivity.
        * rewrite /pack Hbyte /= in Hpack.
          fold pack in Hpack.
          rewrite Hpack' in Hpack.
          discriminate.
      + rewrite /pack Hbyte /= in Hpack.
        discriminate.
  Qed.

  #[local] Lemma pack_WF zs s :
    pack zs = Some s ->
    cstring.WF s.
  Proof.
    revert s.
    induction zs as [|b zs IH]; intros s Hpack; [done|].
    destruct b as [|p].
    - destruct zs as [|b zs].
      + simpl in Hpack. inversion Hpack; subst s.
        apply cstring.WF_nil.
      + done.
    - destruct (Byte.of_N (N.pos p)) as [ch|] eqn:Hbyte.
      + destruct (pack zs) as [s'|] eqn:Hpack'.
        * rewrite /pack Hbyte /= in Hpack.
          fold pack in Hpack.
          rewrite Hpack' in Hpack.
          injection Hpack as <-.
          pose proof (IH s' eq_refl) as Hwf'.
          apply cstring.WF_cons.
          { intro Hzero.
            apply (f_equal Byte.to_N) in Hzero.
            assert (Hto : Byte.to_N ch = N.pos p).
            { apply Byte.to_of_N. exact Hbyte. }
            rewrite Hto in Hzero.
            discriminate. }
          { exact Hwf'. }
        * rewrite /pack Hbyte /= in Hpack.
          fold pack in Hpack.
          rewrite Hpack' in Hpack.
          discriminate.
      + rewrite /pack Hbyte /= in Hpack.
        discriminate.
  Qed.

  #[local] Definition unpack_cstring (bytes : list N) :
      option (cstring.t * list N) :=
    match split_bytes_at_cstring bytes with
    | Some (zs, tail) =>
        match pack zs with
        | Some s => Some (s, tail)
        | None => None
        end
    | None => None
    end.

  #[local] Lemma unpack_cstring_sound bytes s tail :
    unpack_cstring bytes = Some (s, tail) ->
    bytes = cstring.to_zstring s ++ tail /\
    cstring.WF s.
  Proof.
    rewrite /unpack_cstring.
    destruct (split_bytes_at_cstring bytes) as [[zs tail']|] eqn:Hsplit;
      [|done].
    destruct (pack zs) as [s'|] eqn:Hpack; [|done].
    intros Hunpack.
    inversion Hunpack; subst s tail. clear Hunpack.
    pose proof (split_bytes_at_cstring_sound _ _ _ Hsplit) as [Hbytes _].
    pose proof (pack_sound _ _ Hpack) as Hzs.
    pose proof (pack_WF _ _ Hpack) as Hwf.
    split.
    - rewrite Hbytes.
      rewrite Hzs.
      reflexivity.
    - exact Hwf.
  Qed.


  (* Older accepted experiment kept only as a reminder that proof-bearing
     binders inside [\proving{...}] are syntactically accepted. *)
(*
  #[local] Lemma arrayLR_cstring bytes m tail (p : ptr) s :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    p |-> arrayLR "char" 0 m (λ v : N, charR 1$m v) bytes ⊢
    p |-> cstring.R 1$m s ∗
    p |-> arrayLR "char" (m - Zlength tail) m (λ v : N, charR 1$m v) tail.
*)

  #[local] Lemma arrayLR_cstring q bytes m tail (p : ptr) s :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    p |-> arrayLR "char" 0 m (λ v : N, charR q v) bytes ⊢
    [| m = lengthZ bytes |] ∗
    p |-> cstring.R q s ∗
    p |-> arrayLR "char" (m - lengthZ tail) m (λ v : N, charR q v) tail.
  Proof.
    intros -> Hwf.
    rewrite arrayLR.unlock _at_sep lengthN_app.
    arith_simpl.
    iIntros "[%Hlen Harr]".
    rewrite _at_offsetR _at_sub_0; [|done].
    rewrite arrayR_app__N.
    iDestruct "Harr" as "[Hs Htail]".
    assert (H: m - lengthZ tail = lengthZ (cstring.to_zstring s)) by lia.
    rewrite H /cstring.R /zstring.R. iFrame. done.
  Qed.
  Hint Resolve arrayLR_cstring : sl_opacity.

  #[local] Lemma cstring_arrayLR q bytes m tail (p : ptr) s :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    [| m = lengthZ bytes |] ∗
    p |-> cstring.R q s ∗
    p |-> arrayLR "char" (m - lengthZ tail) m (λ v : N, charR q v) tail ⊢
    p |-> arrayLR "char" 0 m (λ v : N, charR q v) bytes.
  Proof.
    intros -> Hwf. work. arith_simpl.
    rewrite lengthN_app. arith_simpl.
    rewrite /cstring.R /zstring.R. work.
    rewrite arrayLR.unlock. arith_simpl. work.
    rewrite _at_sub_0; [trivial|done].
  Qed.
  Hint Resolve cstring_arrayLR : sl_opacity.

  #[local, program] Definition arrayLR_open_cstring_C
      (p : ptr) q k bytes tail
      (Hex : exists s, unpack_cstring bytes = Some (s, tail)) :=
    \cancelx
    \consuming p |-> arrayLR "char" 0 k
                 (λ v : N, charR q v) bytes
    \proving{s (Hunpack : unpack_cstring bytes = Some (s, tail))}
      p |-> cstring.R q s
    \deduce p |-> arrayLR "char" (k - lengthZ tail) k
                (λ v : N, charR q v) tail
    \end@{mpred}.
  Next Obligation.
    intros p q k bytes tail [s0 Hunpack0].
    iIntros "Harr".
    pose proof (unpack_cstring_sound _ _ _ Hunpack0) as [Hbytes0 Hwf0].
    iPoseProof (arrayLR_cstring q bytes k tail p s0 Hbytes0 Hwf0 with "Harr")
      as "(%Hk & Hs0 & Htail)".
    iFrame "Htail".
    iIntros (s Hunpack).
    rewrite Hunpack0 in Hunpack.
    injection Hunpack as <-.
    iExact "Hs0".
  Qed.
  #[local] Hint Resolve arrayLR_open_cstring_C : sl_opacity.

  #[local, program] Definition arrayLR_close_cstring_C
      (p : ptr) q mid k tail s
      (Hmid : mid = lengthZ (cstring.to_zstring s))
      (Htailk : mid = k - lengthZ tail) :=
    \cancelx
    \consuming p |-> cstring.R q s
    \consuming p |-> arrayLR "char" mid k (λ v : N, charR q v) tail
    \proving p |-> arrayLR "char" 0 k
         (λ _ : unit, anyR "char" q) (replicateN (Z.to_N k) ())
    \end@{mpred}.
  Next Obligation.
    intros p q mid k tail s Hmid Htailk.
    iIntros "[Hs Htail]".
    rewrite /cstring.R /zstring.R.
    iDestruct "Hs" as "[Hs %Hwf]".
    assert (Hk : k = lengthZ (cstring.to_zstring s ++ tail)).
    { rewrite lengthN_app. arith_simpl. lia. }
    clear Hmid.
    subst mid.
    iPoseProof
      (cstring_arrayLR q (cstring.to_zstring s ++ tail) k tail p s eq_refl Hwf
        with "[Hs Htail]")
      as "Harr".
    { iSplit.
      - iPureIntro. exact Hk.
      - rewrite /cstring.R /zstring.R.
        iSplitL "Hs".
        + iFrame. iPureIntro. exact Hwf.
        + iFrame "Htail". }
    rewrite Hk N2Z.id.
    iPoseProof (arrayLR_charR_arrayLR_anyR _ q (cstring.to_zstring s ++ tail)
      with "Harr") as "Harr".
    iExact "Harr".
  Qed.
  #[local] Hint Resolve arrayLR_close_cstring_C : sl_opacity.

  (*
    Experimental variants that internalize the unpack witness more aggressively.

    Both [arrayLR_open_cstring_guard_C] and [arrayLR_open_cstring_using_C] are
    provable, but in this file they do not fire under [go]/[ego] at the
    [test_strlen_array_buffer()] call site, even when the matching pure
    existence fact is supplied explicitly in the proof context. We therefore
    keep them parked for design/reference purposes and continue using the
    simpler [arrayLR_open_cstring_C] together with an explicit [Hex] witness in
    the verification proof.

  #[local, program] Definition arrayLR_open_cstring_guard_C
      (p : ptr) q k bytes :=
    \cancelx
    \guard (exists stail, unpack_cstring bytes = Some stail)
    \consuming p |-> arrayLR "char" 0 k
                 (λ v : N, charR q v) bytes
    \deduce{stail} [| unpack_cstring bytes = Some stail |]
    \bound_existential s
    \proving p |-> cstring.R q s
    \instantiate s := fst stail
    \deduce p |-> arrayLR "char" (k - lengthZ (snd stail)) k
                (λ v : N, charR q v) (snd stail)
    \end@{mpred}.
  Next Obligation.
    intros p q k bytes [stail Hunpack0].
    destruct stail as [s0 tail0].
    iIntros "Harr".
    pose proof (unpack_cstring_sound _ _ _ Hunpack0) as [Hbytes0 Hwf0].
    iPoseProof (arrayLR_cstring q bytes k tail0 p s0 Hbytes0 Hwf0 with "Harr")
      as "(%Hk & Hs0 & Htail)".
    iExists (s0, tail0).
    iSplitL "Htail".
    { iSplit.
      - iPureIntro. exact Hunpack0.
      - iFrame. }
    iIntros (??). subst.
    cbn.
    iIntros (?).
    subst.
    iExact "Hs0".
  Qed.

  #[local, program] Definition arrayLR_open_cstring_using_C
      (p : ptr) q k bytes :=
    \cancelx
    \using [| exists stail, unpack_cstring bytes = Some stail |]
    \consuming p |-> arrayLR "char" 0 k
                 (λ v : N, charR q v) bytes
    \deduce{stail} [| unpack_cstring bytes = Some stail |]
    \bound_existential s
    \proving p |-> cstring.R q s
    \instantiate s := fst stail
    \deduce p |-> arrayLR "char" (k - lengthZ (snd stail)) k
                (λ v : N, charR q v) (snd stail)
    \end@{mpred}.
  Next Obligation.
    iIntros (p q k bytes) "[%Hex Harr]".
    destruct Hex as [[s0 tail0] Hunpack0].
    pose proof (unpack_cstring_sound _ _ _ Hunpack0) as [Hbytes0 Hwf0].
    iPoseProof (arrayLR_cstring q bytes k tail0 p s0 Hbytes0 Hwf0 with "Harr")
      as "(%Hk & Hs0 & Htail)".
    iExists (s0, tail0).
    iSplitL "Htail".
    { iSplit.
      - iPureIntro. exact Hunpack0.
      - iFrame. }
    iIntros (??). subst.
    cbn.
    iIntros (?).
    subst.
    iExact "Hs0".
  Qed.
  *)

  cpp.spec "test_strlen_array_buffer()" default.
  Lemma test_strlen_array_buffer_ok :
    verify[module] "test_strlen_array_buffer()".
  Proof.
    verify_spec; go.
    assert (Hex :
      exists s,
        unpack_cstring
          (cstring.to_zstring "ab"%bs ++ [99%N; 100%N; 0%N]) =
        Some (s, [99%N; 100%N; 0%N])) by (eexists; reflexivity).
    ego.
  Qed.

  cpp.spec "test_strcmp_array_buffer()" default.
  Lemma test_strcmp_array_buffer_ok :
    verify[module] "test_strcmp_array_buffer()".
  Proof.
    verify_spec; go.
    assert (Hex :
      exists s,
        unpack_cstring
          (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) =
        Some (s, [120%N; 0%N])) by (eexists; reflexivity).
    assert (Hey :
      exists s,
        unpack_cstring
          (cstring.to_zstring "ab"%bs ++ [121%N; 0%N]) =
        Some (s, [121%N; 0%N])) by (eexists; reflexivity).
    ego.
  Qed.

  cpp.spec "test_strncmp_array_buffer()" default.
  Lemma test_strncmp_array_buffer_ok :
    verify[module] "test_strncmp_array_buffer()".
  Proof.
    verify_spec; go.
    assert (Hex :
      exists s,
        unpack_cstring
          (cstring.to_zstring "ab"%bs ++ [120%N; 0%N]) =
        Some (s, [120%N; 0%N])) by (eexists; reflexivity).
    assert (Hey :
      exists s,
        unpack_cstring
          (cstring.to_zstring "ab"%bs ++ [121%N; 0%N]) =
        Some (s, [121%N; 0%N])) by (eexists; reflexivity).
    ego.
  Qed.

  cpp.spec "test_strchr()" default.
  Lemma test_strchr_ok : verify[module] "test_strchr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strrchr()" default.
  Lemma test_strrchr_ok : verify[module] "test_strrchr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strspn()" default.
  Lemma test_strspn_ok : verify[module] "test_strspn()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strcspn()" default.
  Lemma test_strcspn_ok : verify[module] "test_strcspn()".
  Proof. verify_spec; go; ego. Qed.

  cpp.spec "test_strpbrk()" default.
  Lemma test_strpbrk_ok : verify[module] "test_strpbrk()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_strstr()" default.
  Lemma test_strstr_ok : verify[module] "test_strstr()".
  Proof using MOD.
    verify_spec; go; ego.
    Arith.arith_simpl; go; ego.
    Arith.arith_simpl; go; ego.
  Qed.

  cpp.spec "test_cstring_slice1()" default.
  Lemma test_cstring_slice1_ok : verify[module] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.

End with_cpp.
