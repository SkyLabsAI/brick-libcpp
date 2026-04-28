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

  (* These byte-side wrappers are proved and registered, but in the current
     [test_memset_ok] proof they still do not fire automatically at the
     call-precondition branches where the target is [object_bytes_anyR]. *)
  #[local, program] Definition object_bytesR_object_bytes_any_C
      (p : ptr) q bytes :=
    \cancelx
    \consuming p |-> object_bytesR Tuchar q bytes
    \proving{n (Hlen : n = lengthN bytes)}
      p |-> object_bytes_anyR Tuchar q (Z.of_N n)
    \end@{mpred}.
  Next Obligation.
    intros p q bytes.
    iIntros "Hbytes" (n Hlen).
    iApply (object_bytesR_ucharR_object_bytes_anyR _ q n bytes).
    - rewrite Hlen.
      rewrite /lengthN Nat2N.id.
      reflexivity.
    - iExact "Hbytes".
  Qed.
  #[local] Hint Resolve object_bytesR_object_bytes_any_C : sl_opacity.

  #[local, program] Definition object_bytesR_arrayLR_any_C
      (p : ptr) q bytes :=
    \cancelx
    \consuming p |-> object_bytesR Tuchar q bytes
    \proving{n (Hlen : n = lengthN bytes)}
      p |-> arrayLR Tuchar 0 (Z.of_N n)
         (fun _ : unit => anyR Tuchar q) (replicateN n ())
    \end@{mpred}.
  Next Obligation.
    intros p q bytes.
    iIntros "Hbytes" (n Hlen).
    iApply (object_bytesR_ucharR_arrayLR_anyR _ q n bytes).
    - rewrite Hlen.
      rewrite /lengthN Nat2N.id.
      reflexivity.
    - iExact "Hbytes".
  Qed.
  #[local] Hint Resolve object_bytesR_arrayLR_any_C : sl_opacity.

  #[local] Lemma at_uchar_offset_eq
      (p : ptr) i j (R : Rep) :
    i = j ->
    p |-> .[Tuchar ! i] |-> R ⊢
    p |-> .[Tuchar ! j] |-> R.
  Proof.
    intros ->. reflexivity.
  Qed.

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

  (*
    Planned Family A automation structure for [test_memset()].

    The intended reusable shape is:

    - an outer entry wrapper from the stack-array [arrayLR] view to one wrapped
      [object_bytesR] view
    - a core opening principle for a writable subrange inside a wrapped byte
      region, where the split is computed canonically from the consumed [bytes]
      using [takeZ]/[dropZ]
    - a core closing principle that rebuilds one wrapped byte region after the
      call from preserved prefix, modified middle, and preserved suffix

    This should let instruction 1 be handled as:

    1. wrap the initial array into one [object_bytesR]
    2. open the target subrange for the mutating call
    3. close the post-call modified bytes back into one [object_bytesR]

    and instruction 6 should reuse the same core open/close pair, differing
    only in the chosen offset and active length.

  #[local, program] Definition arrayLR_wrap_object_bytesR_C
      (p : ptr) ty q bytes :=
    \cancelx
    \consuming p |-> arrayLR ty 0 (lengthZ bytes)
                 (fun v : Z => ucharR q v) bytes
    \proving p |-> object_bytesR ty q bytes
    \end@{mpred}.

  #[local, program] Definition object_bytesR_open_range_any_C
      (p : ptr) ty q off len bytes :=
    \cancelx
    \using [| 0 <= off |]
    \using [| 0 <= len |]
    \using [| off + len <= lengthZ bytes |]
    \consuming p |-> object_bytesR ty q bytes
    \proving p .[ty ! off] |-> object_bytes_anyR ty q len
    \deduce p |-> object_bytesR ty q (takeZ off bytes)
    \deduce p .[ty ! (off + len)] |->
      object_bytesR ty q (dropZ (off + len) bytes)
    \end@{mpred}.

  #[local, program] Definition object_bytesR_close_range_C
      (p : ptr) ty q prefix ys suffix :=
    \cancelx
    \consuming p |-> object_bytesR ty q prefix
    \consuming p .[ty ! lengthZ prefix] |-> object_bytesR ty q ys
    \consuming p .[ty ! (lengthZ prefix + lengthZ ys)] |->
      object_bytesR ty q suffix
    \proving p |-> object_bytesR ty q (prefix ++ ys ++ suffix)
    \end@{mpred}.

    Design notes:
    - [arrayLR_wrap_object_bytesR_C] is only the outer boundary adapter; it is
      not the core mutating-call automation.
    - [object_bytesR_open_range_any_C] should only be considered where the
      goal is specifically [object_bytes_anyR], which helps avoid eager firing
      in the read-only assert steps.
    - the opener is phrased in terms of [off] and [len] because those are the
      parameters the next instruction naturally determines; the left prefix,
      active middle slice, and right suffix are then the canonical split
      [takeZ off bytes], [takeZ len (dropZ off bytes)], and
      [dropZ (off + len) bytes].
    - [object_bytesR_close_range_C] is the candidate wrapped-state
      reestablishment step between instructions.
    - if these become real hints, the likely first use is still local to this
      proof family; broad installation would risk spurious firing in other
      byte-API clients.
  *)

  (*
    Parked experiments. These are useful design sketches, but they are not the
    right live automation surface for the current [memset] work:
    [arrayLR_wrap_object_bytesR_C] does not fire even on an exact standalone
    [arrayLR ⊢ object_bytesR] goal, and [object_bytesR_open_range_any_C] does
    not fire on the standalone range-opening workspaces. Keep them aborted
    rather than admitted.

  #[local, program] Definition arrayLR_wrap_object_bytesR_C
      (p : ptr) ty q n bytes :=
    \cancelx
    \consuming p |-> arrayLR ty 0 n
                 (fun v : Z => ucharR q v) bytes
    \proving p |-> object_bytesR ty q bytes
    \end@{mpred}.
  Next Obligation.
    intros p ty q n bytes. iIntros "X".
    iApply object_bytesR_of_arrayLR. 2: iFrame.
  Abort.

  #[local, program] Definition object_bytesR_open_range_any_C
      (p : ptr) ty q off len bytes :=
    \cancelx
    \using [| 0 <= off |]
    \using [| 0 <= len |]
    \using [| off + len <= lengthZ bytes |]
    \consuming p |-> object_bytesR ty q bytes
    \proving p .[ty ! off] |-> object_bytes_anyR ty q len
    \deduce p |-> object_bytesR ty q (takeZ off bytes)
    \deduce p .[ty ! (off + len)] |->
      object_bytesR ty q (dropZ (off + len) bytes)
    \end@{mpred}.
  Next Obligation.
    intros p ty q off len bytes.
    iIntros "[%Hoff [%Hlen [%Hbytes H]]]".
    (*iRewrite - (takeN_dropN) in "H".
    iPoseProof (object_bytesR_prefix_tail0 p ty q (takeZ off bytes) (dropZ off bytes)) as "X".*)
  Abort.
  *)

  #[local, program] Definition arrayLR_open_prefix_any_C
      (p : ptr) q len n bytes
      (Hlen : 0 <= len <= n) :=
    \cancelx
    \consuming p |-> arrayLR Tuchar 0 n
                 (fun v : Z => ucharR q v) bytes
    \proving p |-> object_bytes_anyR Tuchar q len
    \deduce p .[Tuchar ! len] |-> object_bytesR Tuchar q (dropZ len bytes)
    \end@{mpred}.
  Next Obligation.
    intros p q len n bytes Hlen.
    rewrite arrayLR.unlock _at_sep. arith_simpl.
    iIntros "[%Hn Hbytes]".
    rewrite _at_offsetR _at_sub_0; [|done].
    assert (HnN : lengthN bytes = Z.to_N n) by lia.
    assert (Htake : lengthN (takeZ len bytes) = Z.to_N len).
    { rewrite /takeZ lengthN_takeN HnN.
      apply N.min_l.
      apply Z2N.inj_le; lia. }
    assert (Hsplit : takeZ len bytes ++ dropZ len bytes = bytes)
      by exact (takeN_dropN (Z.to_N len) bytes).
    iAssert (p |-> arrayR Tuchar (fun v : Z => ucharR q v)
               (takeZ len bytes ++ dropZ len bytes))
      with "[Hbytes]" as "Hbytes".
    { rewrite Hsplit. iExact "Hbytes". }
    iEval (rewrite (@arrayR_app__N _ _ _ _ Z (fun v : Z => ucharR q v) Tuchar
      (takeZ len bytes) (dropZ len bytes))) in "Hbytes".
    iDestruct "Hbytes" as "[Hpre Htail]".
    iAssert (p |-> object_bytesR Tuchar q (takeZ len bytes))
      with "[Hpre]" as "Hpre_bytes".
    { iApply (object_bytesR_of_arrayLR p Tuchar q len (takeZ len bytes)).
      lia.
      rewrite arrayLR.unlock _at_sep _at_offsetR _at_sub_0 ; [ work; iFrame | done]. }
    iPoseProof (object_bytesR_ucharR_object_bytes_anyR p q
      (lengthN (takeZ len bytes)) (takeZ len bytes)
      ltac:(rewrite Nat2N.id; reflexivity) with "Hpre_bytes") as "Hpre_any".
    rewrite Htake Z2N.id; [ | lia]. iFrame.
    iApply (object_bytesR_of_arrayLR (p.[Tuchar ! len]) Tuchar q
        (lengthZ (dropZ len bytes))
        (dropZ len bytes) eq_refl).
    rewrite arrayLR.unlock. arith_simpl. work; iFrame.
  Qed.
  #[local] Hint Resolve arrayLR_open_prefix_any_C | 1000 : sl_opacity.

  #[local, program] Definition arrayLR_open_prefix_bytes_C
      (p : ptr) q len n bytes
      (Hlen : 0 <= len <= n) :=
    \cancelx
    \consuming p |-> arrayLR Tuchar 0 n
                 (fun v : Z => ucharR q v) bytes
    \proving p |-> object_bytesR Tuchar q (takeZ len bytes)
    \deduce p .[Tuchar ! len] |-> object_bytesR Tuchar q (dropZ len bytes)
    \end@{mpred}.
  Next Obligation.
    intros p q len n bytes Hlen.
    rewrite arrayLR.unlock _at_sep. arith_simpl.
    rewrite _at_offsetR _at_sub_0; [|done].
    iIntros "[%Hn Hbytes]".
    assert (HnN : lengthN bytes = Z.to_N n) by lia.
    assert (Htake : lengthN (takeZ len bytes) = Z.to_N len).
    { rewrite /takeZ lengthN_takeN HnN.
      apply N.min_l.
      apply Z2N.inj_le; lia. }
    assert (Hsplit : takeZ len bytes ++ dropZ len bytes = bytes)
      by exact (takeN_dropN (Z.to_N len) bytes).
    iAssert (p |-> arrayR Tuchar (fun v : Z => ucharR q v)
               (takeZ len bytes ++ dropZ len bytes))
      with "[Hbytes]" as "Hbytes".
    { rewrite Hsplit. iExact "Hbytes". }
    iEval (rewrite (@arrayR_app__N _ _ _ _ Z (fun v : Z => ucharR q v) Tuchar
      (takeZ len bytes) (dropZ len bytes))) in "Hbytes".
    iDestruct "Hbytes" as "[Hpre Htail]".
    iAssert (p |-> object_bytesR Tuchar q (takeZ len bytes))
      with "[Hpre]" as "Hpre_bytes".
    { iApply (object_bytesR_of_arrayLR p Tuchar q len (takeZ len bytes)).
      lia.
      rewrite arrayLR.unlock _at_sep _at_offsetR _at_sub_0; [work; iFrame | done]. }
    iFrame "Hpre_bytes".
    iPoseProof (at_uchar_offset_eq p (lengthZ (takeZ len bytes)) len
      (arrayR Tuchar (fun v : Z => ucharR q v) (dropZ len bytes))
      ltac:(unfold lengthZ; rewrite Htake; apply Z2N.id; lia)
      with "Htail") as "Htail".
    iApply (object_bytesR_of_arrayLR (p.[Tuchar ! len]) Tuchar q
      (lengthZ (dropZ len bytes))
      (dropZ len bytes) eq_refl).
    rewrite arrayLR.unlock. arith_simpl. work; iFrame.
  Qed.
  #[local] Hint Resolve arrayLR_open_prefix_bytes_C | 1000 : sl_opacity.

  (*
    The generic wrapper/openers above are useful proof principles, but the
    workspace lemmas below show a mixed picture:
    - both the earlier [lengthZ bytes]-surface and the newer [n]-surface for
      [arrayLR_wrap_object_bytesR_C] fail to fire even on an exact standalone
      [arrayLR ⊢ object_bytesR] goal.
    - [object_bytesR_open_range_any_C] likewise leaves the standalone range
      goals unchanged, even when the relevant bounds are available as ordinary
      Rocq hypotheses.
    - the earlier [lengthZ bytes]-surface for [arrayLR_open_prefix_any_C] left
      both the real first-call state and the standalone prefix-opening goals
      unchanged.
    - the newer [n]-surface for [arrayLR_open_prefix_any_C] does move the real
      [verify_spec] first-call workspace to the post-call state, but it still
      does not solve the standalone prefix-opening toy goals.
    - so the best current reading is that a sufficiently direct opener can be
      useful at the real mutating-call surface even if it is not a generally
      useful entailment hint.
  *)

  (*
    Parked experiments that are no longer needed to reach the current memset
    workspace state.

  #[local, program] Definition memset_open_2_C (p : ptr) :=
    \cancelx
    \consuming p |-> arrayLR Tuchar 0 4
                 (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]
    \proving p |-> object_bytes_anyR Tuchar 1$m 2
    \deduce p .[Tuchar ! 2] |-> object_bytesR Tuchar 1$m [99%Z; 100%Z]
    \end@{mpred}.
  Next Obligation. Admitted.

  #[local] Lemma object_bytesR_read_head_after_open
      (p : ptr) q off x xs suffix :
    p .[Tuchar ! off] |-> object_bytesR Tuchar q (x :: xs) ∗
    p .[Tuchar ! (off + 1 + lengthZ xs)] |-> object_bytesR Tuchar q suffix ⊢
    p .[Tuchar ! off] |-> primR Tuchar q (Vint x) ∗
    p .[Tuchar ! (off + 1)] |-> object_bytesR Tuchar q (xs ++ suffix).
  Admitted.
  *)

  #[local] Lemma object_bytesR_read_head_uchar_after_open
      (p : ptr) q off x xs suffix :
    p .[Tuchar ! off] |-> object_bytesR Tuchar q (x :: xs) ∗
    p .[Tuchar ! (off + lengthZ (x :: xs))] |-> object_bytesR Tuchar q suffix ⊢
    p .[Tuchar ! off] |-> ucharR q x ∗
    p .[Tuchar ! (off + 1)] |-> object_bytesR Tuchar q (xs ++ suffix).
  Proof.
    iIntros "[Hhead Hsuffix]".
    assert (Hhead_total : lengthZ (x :: xs) = 1 + lengthZ xs).
    { assert (Hlen_consN : lengthN (x :: xs) = N.succ (lengthN xs)).
      { unfold lengthN.
        simpl.
        rewrite Nat2N.inj_succ.
        reflexivity. }
      unfold lengthZ.
      rewrite Hlen_consN.
      destruct (lengthN xs); simpl; lia. }
    iPoseProof (at_uchar_offset_add_intro p off (1 + lengthZ xs)
      (off + lengthZ (x :: xs)) (object_bytesR Tuchar q suffix)
      ltac:(rewrite Hhead_total; lia) with "Hsuffix") as "Hsuffix".
    iPoseProof (at_uchar_offset_add_intro (p .[Tuchar ! off]) 1 (lengthZ xs)
      (1 + lengthZ xs) (object_bytesR Tuchar q suffix)
      ltac:(lia) with "Hsuffix") as "Hsuffix".
    iPoseProof ((object_bytesR_prefix_tail0 (p .[Tuchar ! off]) Tuchar q
      1 (1 + lengthZ xs) [x] xs
      ltac:(rewrite Hhead_total; reflexivity)
      ltac:(reflexivity) ltac:(lia))
      with "Hhead") as "[Hx Hxs]".
    iPoseProof (object_bytesR_ucharR_arrayR (p .[Tuchar ! off]) q [x]
      with "Hx") as "Hx".
    iPoseProof (at_arrayR_ucharR_cons (p .[Tuchar ! off]) q x [] with "Hx")
      as "(#Hty & Hx & _)".
    assert (Hxs_suffix_total : lengthZ (xs ++ suffix) = lengthZ xs + lengthZ suffix).
    { assert (Hsum : lengthZ (xs ++ suffix) = Z.of_N (lengthN xs + lengthN suffix)).
      { apply lengthZ_of_to_nat_length.
        rewrite N2Nat.inj_add.
        unfold lengthN.
        rewrite !Nat2N.id.
        rewrite List.length_app.
        reflexivity. }
      rewrite Hsum.
      unfold lengthZ.
      destruct (lengthN xs), (lengthN suffix); simpl; lia. }
    assert (Hsuffix_len : lengthZ suffix = lengthZ (xs ++ suffix) - lengthZ xs) by lia.
    iPoseProof ((object_bytesR_prefix_tail0 (p .[Tuchar ! off] .[Tuchar ! 1])
      Tuchar q (lengthZ xs) (lengthZ (xs ++ suffix)) xs suffix
      ltac:(reflexivity) ltac:(reflexivity) ltac:(exact Hsuffix_len))
      with "[$Hxs $Hsuffix]") as "Hrest".
    iPoseProof (at_uchar_offset_add_elim p off 1 (off + 1)
      (object_bytesR Tuchar q (xs ++ suffix)) ltac:(lia) with "Hrest")
      as "Hrest".
    iFrame "Hx Hrest".
  Qed.

  #[local] Lemma object_bytesR_ucharR_ucharR_arrayLR_anyR
      (p : ptr) prefix x y :
    p |-> object_bytesR Tuchar 1$m prefix ∗
    p .[Tuchar ! lengthZ prefix] |-> ucharR 1$m x ∗
    p .[Tuchar ! (lengthZ prefix + 1)] |-> ucharR 1$m y ⊢
    p |-> arrayLR Tuchar 0 (lengthZ (prefix ++ [x; y]))
      (fun _ : unit => anyR Tuchar 1$m)
      (replicateN (lengthN (prefix ++ [x; y])) ()).
  Proof.
    iIntros "(Hprefix & Hx & Hy)".
    iPoseProof (at_uchar_offset_add_intro p (lengthZ prefix) 1
      (lengthZ prefix + 1) (ucharR 1$m y) ltac:(lia) with "Hy") as "Hy".
    iPoseProof (uchar_cells_object_bytesR_two (p .[Tuchar ! lengthZ prefix]) x y
      with "[$Hx $Hy]") as "Htail".
    assert (Htail_len : lengthZ [x; y] = lengthZ (prefix ++ [x; y]) - lengthZ prefix).
    { assert (HsumN : lengthN (prefix ++ [x; y]) = (lengthN prefix + lengthN [x; y])%N).
      { unfold lengthN.
        rewrite List.length_app Nat2N.inj_add.
        reflexivity. }
      unfold lengthZ.
      rewrite HsumN.
      simpl.
      destruct (lengthN prefix); simpl; lia. }
    iPoseProof ((object_bytesR_prefix_tail0 p Tuchar 1$m
      (lengthZ prefix) (lengthZ (prefix ++ [x; y])) prefix [x; y]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(exact Htail_len))
      with "[$Hprefix $Htail]") as "Hall".
    iApply (object_bytesR_ucharR_arrayLR_anyR _ 1$m (lengthN (prefix ++ [x; y]))
      (prefix ++ [x; y])).
    rewrite Nat2N.id. reflexivity.
    iExact "Hall".
  Qed.

  (*
    Parked read-step automation experiments. They were useful to probe whether
    the first read after opening could be automated directly, but they are not
    needed to reach the current best workspace checkpoint below.

  #[local, program] Definition object_bytesR_read_head_C
      (p : ptr) q off x xs suffix :=
    \cancelx
    \consuming p .[Tuchar ! off] |-> object_bytesR Tuchar q (x :: xs)
    \consuming p .[Tuchar ! (off + 1 + lengthZ xs)] |->
      object_bytesR Tuchar q suffix
    \proving p .[Tuchar ! off] |-> primR Tuchar q (Vint x)
    \deduce p .[Tuchar ! (off + 1)] |-> object_bytesR Tuchar q (xs ++ suffix)
    \end@{mpred}.
  Next Obligation.
  Admitted.

  #[local, program] Definition object_bytesR_read_head_bytes_C
      (p : ptr) q off n bytes suffix
      (Hn : n = lengthZ bytes)
      (Hlen : 1 <= n) :=
    \cancelx
    \consuming p .[Tuchar ! off] |-> object_bytesR Tuchar q bytes
    \consuming p .[Tuchar ! (off + n)] |-> object_bytesR Tuchar q suffix
    \proving p .[Tuchar ! off] |-> primR Tuchar q (Vint (hd 0 bytes))
    \deduce p .[Tuchar ! (off + 1)] |->
      object_bytesR Tuchar q (dropZ 1 bytes ++ suffix)
    \end@{mpred}.
  Next Obligation.
  Admitted.

  #[local, program] Definition object_bytesR_read_head_assert_C
      (p : ptr) q off n bytes suffix
      (Hn : n = lengthZ bytes)
      (Hlen : 1 <= n) :=
    \cancelx
    \consuming p .[Tuchar ! off] |-> object_bytesR Tuchar q bytes
    \consuming p .[Tuchar ! (off + n)] |-> object_bytesR Tuchar q suffix
    \bound k
    \proving p .[Tuchar ! off] |-> primR Tuchar q (Vint (hd 0 bytes))
    \goal_trigger (p .[Tuchar ! off] |->
      primR Tuchar q (Vint (hd 0 bytes)) -∗ k)
    \deduce p .[Tuchar ! (off + 1)] |->
      object_bytesR Tuchar q (dropZ 1 bytes ++ suffix)
    \end@{mpred}.
  Next Obligation.
  Admitted.
  #[local] Hint Resolve object_bytesR_read_head_assert_C | 1000 : sl_opacity.

  #[local, program] Definition object_bytesR_read_head_assert_exact_C
      (p : ptr) q off n bytes suffix
      (Hn : n = lengthZ bytes)
      (Hlen : 1 <= n) :=
    \cancelx
    \consuming p .[Tuchar ! off] |-> object_bytesR Tuchar q bytes
    \consuming p .[Tuchar ! (off + n)] |-> object_bytesR Tuchar q suffix
    \bound k
    \bound_existential q'
    \bound_existential v
    \instantiate q' := q
    \instantiate v := Vint (hd 0 bytes)
    \proving p .[Tuchar ! off] |-> primR Tuchar q' v
    \goal_trigger (p .[Tuchar ! off] |-> primR Tuchar q' v -∗ k)
    \whole_conclusion
    \deduce p .[Tuchar ! (off + 1)] |->
      object_bytesR Tuchar q (dropZ 1 bytes ++ suffix)
    \end@{mpred}.
  Next Obligation.
  Admitted.
  #[local] Hint Resolve object_bytesR_read_head_assert_exact_C | 1000 : sl_opacity.

  #[local, program] Definition ucharR_assert_read_B
      (p : ptr) q x :=
    \cancelx
    \bound k
    \proving p |-> primR Tuchar q (Vint x) ∗
              (p |-> primR Tuchar q (Vint x) -∗ k)
    \through p |-> ucharR q x ∗
             (p |-> ucharR q x -∗ k)
    \end@{mpred}.
  Next Obligation.
  Admitted.
  #[local] Hint Resolve ucharR_assert_read_B | 1000 : sl_opacity.

  #[local, program] Definition ucharR_assert_read_C
      (p : ptr) q x :=
    \cancelx
    \consuming p |-> ucharR q x
    \bound k
    \proving p |-> primR Tuchar q (Vint x)
    \goal_trigger (p |-> primR Tuchar q (Vint x) -∗ k)
    \end@{mpred}.
  Next Obligation.
  Admitted.
  #[local] Hint Resolve ucharR_assert_read_C | 1000 : sl_opacity.
  *)

  cpp.spec "test_memset()" default.
  Lemma test_memset_ok : verify[module] "test_memset()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iExists Tuchar.
    ego.
    change (memset 120 2) with [120%Z; 120%Z].
    change (lengthZ [120%Z; 120%Z]) with 2%Z.
    iAssert (
      s_addr .[Tuchar ! 2] |-> object_bytesR Tuchar 1$m
        (dropZ 2 [97%Z; 98%Z; 99%Z; 100%Z]))%I with "[$]" as "Htail".
    iPoseProof (at_zero_intro s_addr
      (object_bytesR Tuchar 1$m [120%Z; 120%Z]) with "[$]") as "Hmid".
    iPoseProof (object_bytesR_read_head_uchar_after_open
      s_addr (cQp.mk false 1%Qp) 0 120%Z [120%Z]
      (dropZ 2 [97%Z; 98%Z; 99%Z; 100%Z])
      with "[$Hmid $Htail]") as "[H0 Hrest]".
    (* Read back the first modified byte: [assert(s[0] == 'x');]. *)
    iSplitL "H0"; [ iExact "H0" | iIntros "H0"].
    (* Now we are onto the next C++ instruction: [assert(s[1] == 'x');]. *)
    go.
    iPoseProof (object_bytesR_arrayLR_cons (s_addr .[Tuchar ! 1]) 120%Z
      (dropZ 2 [97%Z; 98%Z; 99%Z; 100%Z]) with "Hrest")
      as "[[#Hty1 H1] Hrest]".
    iPoseProof (at_zero_elim (s_addr .[Tuchar ! 1]) with "H1") as "H1".
    (* Read back the second modified byte: [assert(s[1] == 'x');]. *)
    iExists (Vint 120%Z), (cQp.mk false 1%Qp); iFrame "H1"; iIntros "H1".
    (* Now we are onto the next C++ instruction: [assert(s[2] == 'c');]. *)
    go.
    change (dropZ 2 [97%Z; 98%Z; 99%Z; 100%Z]) with [99%Z; 100%Z].
    change (lengthZ (120%Z :: [99%Z; 100%Z])) with 3%Z.
    iEval (rewrite (arrayLR_cons (s_addr .[Tuchar ! 1]) 1 3
      (fun b : Z => ucharR 1$m b) 99%Z [100%Z])) in "Hrest".
    iDestruct "Hrest" as "[[#Hty2 H2] Hrest]".
    iPoseProof (at_uchar_offset_add_elim s_addr 1 1 2
      (ucharR 1$m 99%Z) ltac:(lia) with "H2") as "H2".
    iExists (Vint 99%Z), (cQp.mk false 1%Qp); iFrame "H2"; iIntros "H2".
    (* Now we are onto the next C++ instruction: [assert(s[3] == 'd');]. *)
    go.
    iEval (rewrite (arrayLR_cons (s_addr .[Tuchar ! 1]) 2 3
      (fun b : Z => ucharR 1$m b) 100%Z [])) in "Hrest".
    iDestruct "Hrest" as "[[#Hty3 H3] _]".
    iPoseProof (at_uchar_offset_add_elim s_addr 1 2 3
      (ucharR 1$m 100%Z) ltac:(lia) with "H3") as "H3".
    iExists (Vint 100%Z), (cQp.mk false 1%Qp); iFrame "H3"; iIntros "H3".
    (* Now we are onto the next C++ instruction:
       [assert(std::memset(s + 2, 0x123, 1) == s + 2);]. *)
    go.
    iPoseProof (at_zero_elim s_addr with "H0") as "H0".
    iPoseProof (uchar_cells_object_bytesR_two s_addr 120%Z 120%Z
      with "[$H0 $H1]") as "Hhead".
    Arith.arith_simpl.
    iPoseProof (at_uchar_offset_add_intro s_addr 2 1 3
      (ucharR 1$m 100%Z) ltac:(lia) with "H3") as "H3".
    iPoseProof (uchar_cells_object_bytesR_two (s_addr .[Tuchar ! 2])
      99%Z 100%Z with "[$H2 $H3]") as "Htail".
    iPoseProof (object_bytesR_prefix_tail0 (s_addr .[Tuchar ! 2])
      Tuchar (cQp.mk false 1) 1 2 [99%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Htail")
      as "[Htarget Htail]".
    iExists Tuchar.
    iSplitL "Htarget".
    { iApply (object_bytesR_ucharR_object_bytes_anyR _ 1$m 1%N
        [99%Z] ltac:(reflexivity) with "Htarget"). }
    iIntros "Htarget".
    go.
    change (memset 291 1) with [35%Z].
    iPoseProof (at_uchar_offset_add_elim s_addr 2 1 3
      (object_bytesR Tuchar 1$m [100%Z]) ltac:(lia) with "Htail") as "Htail".
    iPoseProof (object_bytesR_read_head_uchar_after_open
      s_addr (cQp.mk false 1%Qp) 2 35%Z []
      [100%Z] with "[$Htarget $Htail]") as "[H2' Htail]".
    iExists (Vint 35%Z), (cQp.mk false 1%Qp); iFrame "H2'"; iIntros "H2'".
    (* Now we are onto the next C++ instruction: [assert(s[3] == 'd');]. *)
    go.
    iPoseProof (object_bytesR_arrayLR_cons (s_addr .[Tuchar ! 3]) 100%Z []
      with "Htail") as "[[#Hty3' H3'] _]".
    iPoseProof (at_zero_elim (s_addr .[Tuchar ! 3]) with "H3'") as "H3'".
    iExists (Vint 100%Z), (cQp.mk false 1%Qp); iFrame "H3'"; iIntros "H3'".
    (* Now we are onto establishing the postcondition. *)
    go.
    iPoseProof (object_bytesR_ucharR_ucharR_arrayLR_anyR s_addr
      [120%Z; 120%Z] 35%Z 100%Z with "[$Hhead $H2' $H3']") as "Hs".
    iFrame "Hs".
    go.
  Qed.

  cpp.spec "test_memchr()" default.
  Lemma test_memchr_ok : verify[module] "test_memchr()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (s_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 97%Z]) as "Hs".
    iPoseProof (object_bytesR_of_arrayLR s_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 97%Z] ltac:(reflexivity) with "Hs") as "Hs".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit.
      + done.
      + iIntros "Hs".
        rewrite (memchr_found_after_prefix (@nil Z) 97%Z [98%Z; 99%Z; 97%Z] 97%Z); [|solve_memchr_side..].
        Arith.arith_simpl; go.
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [97%Z; 98%Z] 99%Z [97%Z] 99%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iFrame|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_missing_if_no_match [97%Z; 98%Z; 99%Z; 97%Z] 122%Z); [|solve_memchr_side..].
    go.
    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 0 4 [] [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Hempty Hs]".
    iExists Tuchar, (cQp.mk false 1), [].
    iSplitL "Hempty"; [iExact "Hempty"|].
    iSplit; [done|].
    iIntros "Hempty".
    go.
    iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 0 4 [] [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hempty $Hs]")
      as "Hs".
    iPoseProof (object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hs")
      as "[Hhead Hs]".
    iExists Tuchar, (cQp.mk false 1), [98%Z; 99%Z; 97%Z].
    iSplitL "Hs"; [iExact "Hs"|].
    iSplit; [done|].
    iIntros "Hs".
    rewrite (memchr_found_after_prefix [98%Z; 99%Z] 97%Z (@nil Z) 97%Z); [|solve_memchr_side..].
    Arith.arith_simpl; go.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 s_addr Tuchar
      (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hhead $Hs]")
      as "Hs".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
      [97%Z; 98%Z; 99%Z; 97%Z]
      ltac:(reflexivity) with "Hs") as "Hs".
    iFrame "Hs".
    go.
    rewrite o_sub_sub in H.
    simpl in H.
    contradiction.
  Qed.

  cpp.spec "test_memcpy()" default.
(*
  Lemma test_memcpy_ok : verify[module] "test_memcpy()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (src_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]) as "Hsrc".
    iDestruct select (dst_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [119%Z; 120%Z; 121%Z; 122%Z]) as "Hdst".

    iPoseProof (object_bytesR_of_arrayLR src_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc") as "Hsrc".

    iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
      (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc")
      as "[Hsrc_copy Hsrc_tail]".

    iPoseProof (object_bytesR_of_arrayLR dst_addr Tuchar (cQp.mk false 1)
      4 [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst") as "Hdst".
    iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
      (cQp.mk false 1) 3 4 [119%Z; 120%Z; 121%Z] [122%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst")
      as "[Hdst_copy Hdst_tail]".

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iExists Tuchar.
    iSplitL "Hsrc_copy"; [iExact "Hsrc_copy"|].
    iSplitL "Hdst_copy".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 3%N
        [119%Z; 120%Z; 121%Z] ltac:(reflexivity) with "Hdst_copy").
    - iSplit; [done|].
      iIntros "[Hsrc_copy Hdst_copy]".
      Arith.arith_simpl.
      go.

      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_copy $Hsrc_tail]") as "Hsrc".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_copy $Hdst_tail]") as "Hdst".

      iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
        [98%Z; 99%Z; 122%Z] with "Hdst") as "[[#Hdst_ty0 Hdst0] Hdst]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty1 Hdst1] Hdst]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty2 Hdst2] Hdst]".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
        122%Z [])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty3 Hdst3] Hdst_empty]".
      iExists (Vint 122%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (object_bytesR_arrayLR_cons src_addr 97%Z
        [98%Z; 99%Z; 100%Z] with "Hsrc") as "[[#Hsrc_ty0 Hsrc0] Hsrc]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc0". iIntros "Hsrc0".
      go.

      iEval (rewrite (arrayLR_cons src_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty1 Hsrc1] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty2 Hsrc2] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty3 Hsrc3] Hsrc_empty2]".
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc3". iIntros "Hsrc3".
      go.

      iPoseProof (at_zero_elim src_addr with "Hsrc0") as "Hsrc0".
      iPoseProof (uchar_cells_object_bytesR_two src_addr 97%Z 98%Z
        with "[$Hsrc0 $Hsrc1]") as "Hsrc_head".
      iPoseProof (at_uchar_offset_add_intro src_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hsrc3") as "Hsrc3".
      iPoseProof (uchar_cells_object_bytesR_two (src_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$Hsrc2 $Hsrc3]") as "Hsrc_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_head $Hsrc_tail2]") as "Hsrc_full".

      iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
      iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
        with "[$Hdst0 $Hdst1]") as "Hdst_head".
      iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
        (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
        99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".

      iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc_full")
        as "[Hsrc_prefix Hsrc_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
        (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hsrc_suffix") as "[Hsrc_empty Hsrc_suffix]".

      iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst_full")
        as "[Hdst_head1 Hdst_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hdst_suffix") as "[Hdst_empty1 Hdst_suffix1]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty1".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 0%N
          [] ltac:(reflexivity) with "Hdst_empty1").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty1]".
        Arith.arith_simpl.
        go.

        iPoseProof ((object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
          (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_empty $Hsrc_suffix]") as "Hsrc_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_prefix $Hsrc_suffix]") as "Hsrc_full".

        iPoseProof ((object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_empty1 $Hdst_suffix1]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
          [98%Z; 99%Z; 122%Z] with "Hdst_full")
          as "[[#Hdst_ty4 Hdst0] Hdst_arr]".
        iExists (Vint 97%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst0". iIntros "Hdst0".
        go.

        iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
          98%Z [99%Z; 122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty5 Hdst1] Hdst_arr]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full") as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
          99%Z [122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty6 Hdst2] Hdst_arr]".
        iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
          122%Z [])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty7 Hdst3] Hdst_empty2]".
        iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
          (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
        iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
          99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 4%N
          [97%Z; 98%Z; 99%Z; 122%Z] ltac:(reflexivity) with "Hdst_full") as "Hdst_any".
        iFrame "Hsrc_any Hdst_any".
        go.
  Qed.

      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_copy $Hsrc_tail]") as "Hsrc".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 3 4 [97%Z; 98%Z; 99%Z] [122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_copy $Hdst_tail]") as "Hdst".

      iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
        [98%Z; 99%Z; 122%Z] with "Hdst") as "[[#Hdst_ty0 Hdst0] Hdst]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty1 Hdst1] Hdst]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [122%Z])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty2 Hdst2] Hdst]".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
        122%Z [])) in "Hdst".
      iDestruct "Hdst" as "[[#Hdst_ty3 Hdst3] Hdst_empty]".
      iExists (Vint 122%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (object_bytesR_arrayLR_cons src_addr 97%Z
        [98%Z; 99%Z; 100%Z] with "Hsrc") as "[[#Hsrc_ty0 Hsrc0] Hsrc]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc0". iIntros "Hsrc0".
      go.

      iEval (rewrite (arrayLR_cons src_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty1 Hsrc1] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty2 Hsrc2] Hsrc]".
      iEval (rewrite (arrayLR_cons src_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hsrc".
      iDestruct "Hsrc" as "[[#Hsrc_ty3 Hsrc3] Hsrc_empty2]".
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "Hsrc3". iIntros "Hsrc3".
      go.

      iPoseProof (at_zero_elim src_addr with "Hsrc0") as "Hsrc0".
      iPoseProof (uchar_cells_object_bytesR_two src_addr 97%Z 98%Z
        with "[$Hsrc0 $Hsrc1]") as "Hsrc_head".
      iPoseProof (at_uchar_offset_add_intro src_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hsrc3") as "Hsrc3".
      iPoseProof (uchar_cells_object_bytesR_two (src_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$Hsrc2 $Hsrc3]") as "Hsrc_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hsrc_head $Hsrc_tail2]") as "Hsrc_full".

      iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
      iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
        with "[$Hdst0 $Hdst1]") as "Hdst_head".
      iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
        (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
        99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".

      iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc_full")
        as "[Hsrc_prefix Hsrc_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
        (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hsrc_suffix") as "[Hsrc_empty Hsrc_suffix]".

      iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst_full")
        as "[Hdst_head1 Hdst_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hdst_suffix") as "[Hdst_empty1 Hdst_suffix1]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty1".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 1$m 0%N
          [] ltac:(reflexivity) with "Hdst_empty1").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty1]".
        Arith.arith_simpl.
        go.

        iPoseProof ((object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 2]) Tuchar
          (cQp.mk false 1) 0 2 [] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_empty $Hsrc_suffix]") as "Hsrc_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_prefix $Hsrc_suffix]") as "Hsrc_full".

        iPoseProof ((object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_empty1 $Hdst_suffix1]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
          [98%Z; 99%Z; 122%Z] with "Hdst_full")
          as "[[#Hdst_ty4 Hdst0] Hdst_arr]".
        iExists (Vint 97%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst0". iIntros "Hdst0".
        go.

        iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
          98%Z [99%Z; 122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty5 Hdst1] Hdst_arr]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full") as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
          99%Z [122%Z])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty6 Hdst2] Hdst_arr]".
        iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
          122%Z [])) in "Hdst_arr".
        iDestruct "Hdst_arr" as "[[#Hdst_ty7 Hdst3] Hdst_empty2]".
        iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
          (ucharR 1$m 122%Z) ltac:(lia) with "Hdst3") as "Hdst3".
        iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
          99%Z 122%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 122%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
          [97%Z; 98%Z; 99%Z; 122%Z] ltac:(reflexivity) with "Hdst_full") as "Hdst_any".
        iFrame "Hsrc_any Hdst_any".
        go.
        *)

  cpp.spec "test_memmove()" default.
  Lemma test_memmove_ok : verify[module] "test_memmove()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (src_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z; 100%Z]) as "Hsrc".
    iDestruct select (dst_addr |-> arrayLR Tuchar 0 4
      (fun v : Z => ucharR 1$m v) [119%Z; 120%Z; 121%Z; 122%Z]) as "Hdst".

    iPoseProof (object_bytesR_of_arrayLR src_addr Tuchar (cQp.mk false 1)
      4 [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc") as "Hsrc".
    iPoseProof (object_bytesR_of_arrayLR dst_addr Tuchar (cQp.mk false 1)
      4 [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst") as "Hdst".

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z; 100%Z].
    iExists Tuchar.
    iSplitL "Hsrc"; [iExact "Hsrc"|].
    iSplitL "Hdst".
    - iApply (object_bytesR_ucharR_object_bytes_anyR _ 1$m 4%N
        [119%Z; 120%Z; 121%Z; 122%Z] ltac:(reflexivity) with "Hdst").
    - iSplit; [done|].
      iIntros "[Hsrc Hdst]".
      Arith.arith_simpl.
      go.

      iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
        [98%Z; 99%Z; 100%Z] with "Hdst") as "[[#Hdst_ty0 Hdst0] Hdst_arr]".
      iExists (Vint 97%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst0". iIntros "Hdst0".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
        98%Z [99%Z; 100%Z])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty1 Hdst1] Hdst_arr]".
      iExists (Vint 98%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst1". iIntros "Hdst1".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
        99%Z [100%Z])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty2 Hdst2] Hdst_arr]".
      Arith.arith_simpl.
      iExists (Vint 99%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst2". iIntros "Hdst2".
      go.

      iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
        100%Z [])) in "Hdst_arr".
      iDestruct "Hdst_arr" as "[[#Hdst_ty3 Hdst3] Hdst_empty0]".
      iExists (Vint 100%Z), (cQp.mk false 1%Qp).
      iFrame "Hdst3". iIntros "Hdst3".
      go.

      iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
      iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
        with "[$Hdst0 $Hdst1]") as "Hdst_head".
      iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
        (ucharR 1$m 100%Z) ltac:(lia) with "Hdst3") as "Hdst3".
      iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
        99%Z 100%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
      iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
        with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".

      iPoseProof (object_bytesR_prefix_tail0 src_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hsrc")
        as "[Hsrc_head1 Hsrc_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hsrc_suffix") as "[Hsrc_empty Hsrc_suffix]".

      iPoseProof (object_bytesR_prefix_tail0 dst_addr Tuchar
        (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hdst_full")
        as "[Hdst_head1 Hdst_suffix]".
      iPoseProof (object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
        (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
        ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        with "Hdst_suffix") as "[Hdst_empty1 Hdst_suffix1]".

      iExists Tuchar, (cQp.mk false 1), [].
      iExists Tuchar.
      iSplitL "Hsrc_empty"; [iExact "Hsrc_empty"|].
      iSplitL "Hdst_empty1".
      + iApply (object_bytesR_ucharR_object_bytes_anyR _ 1$m 0%N
          [] ltac:(reflexivity) with "Hdst_empty1").
      + iSplit; [done|].
        iIntros "[Hsrc_empty Hdst_empty1]".
        Arith.arith_simpl.
        go.

        iPoseProof ((object_bytesR_prefix_tail0 (src_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_empty $Hsrc_suffix]") as "Hsrc_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 src_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hsrc_head1 $Hsrc_suffix]") as "Hsrc_full".

        iPoseProof ((object_bytesR_prefix_tail0 (dst_addr .[Tuchar ! 1]) Tuchar
          (cQp.mk false 1) 0 3 [] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_empty1 $Hdst_suffix1]") as "Hdst_suffix".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 1 4 [97%Z] [98%Z; 99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head1 $Hdst_suffix]") as "Hdst_full".

        iPoseProof (object_bytesR_arrayLR_cons dst_addr 97%Z
          [98%Z; 99%Z; 100%Z] with "Hdst_full")
          as "[[#Hdst_ty4 Hdst0] Hdst_arr2]".
        iEval (rewrite (arrayLR_cons dst_addr 1 4 (fun b : Z => ucharR 1$m b)
          98%Z [99%Z; 100%Z])) in "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[[#Hdst_ty5 Hdst1] Hdst_arr2]".
        iExists (Vint 98%Z), (cQp.mk false 1%Qp).
        iFrame "Hdst1". iIntros "Hdst1".
        go.

        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hsrc_full")
          as "Hsrc_any".
        iPoseProof (at_zero_elim dst_addr with "Hdst0") as "Hdst0".
        iPoseProof (uchar_cells_object_bytesR_two dst_addr 97%Z 98%Z
          with "[$Hdst0 $Hdst1]") as "Hdst_head".
        iEval (rewrite (arrayLR_cons dst_addr 2 4 (fun b : Z => ucharR 1$m b)
          99%Z [100%Z])) in "Hdst_arr2".
        iDestruct "Hdst_arr2" as "[[#Hdst_ty6 Hdst2] Hdst_arr3]".
        iEval (rewrite (arrayLR_cons dst_addr 3 4 (fun b : Z => ucharR 1$m b)
          100%Z [])) in "Hdst_arr3".
        iDestruct "Hdst_arr3" as "[[#Hdst_ty7 Hdst3] Hdst_empty2]".
        iPoseProof (at_uchar_offset_add_intro dst_addr 2 1 3
          (ucharR 1$m 100%Z) ltac:(lia) with "Hdst3") as "Hdst3".
        iPoseProof (uchar_cells_object_bytesR_two (dst_addr .[Tuchar ! 2])
          99%Z 100%Z with "[$Hdst2 $Hdst3]") as "Hdst_tail2".
        iPoseProof ((object_bytesR_prefix_tail0 dst_addr Tuchar
          (cQp.mk false 1) 2 4 [97%Z; 98%Z] [99%Z; 100%Z]
          ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
          with "[$Hdst_head $Hdst_tail2]") as "Hdst_full".
        iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 4%N
          [97%Z; 98%Z; 99%Z; 100%Z] ltac:(reflexivity) with "Hdst_full")
          as "Hdst_any".
        iFrame "Hsrc_any Hdst_any".
        go.
  Qed.

  cpp.spec "test_memcmp()" default.
  Lemma test_memcmp_ok : verify[module] "test_memcmp()".
  Proof using MOD _Σ thread_info Σ σ.
    verify_spec; go.
    iDestruct select (abc_addr |-> arrayLR Tuchar 0 3
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 99%Z]) as "Habc".
    iDestruct select (abd_addr |-> arrayLR Tuchar 0 3
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z; 100%Z]) as "Habd".
    iDestruct select (ab_addr |-> arrayLR Tuchar 0 2
      (fun v : Z => ucharR 1$m v) [97%Z; 98%Z]) as "Hab".

    iPoseProof (object_bytesR_of_arrayLR abc_addr Tuchar (cQp.mk false 1)
      3 [97%Z; 98%Z; 99%Z] ltac:(reflexivity) with "Habc") as "Habc".
    iPoseProof (object_bytesR_half_split with "Habc") as
      "[Habc_left Habc_right]".
    iExists Tuchar, (cQp.mk false (1/2)), [97%Z; 98%Z; 99%Z].
    iExists Tuchar, (cQp.mk false (1/2)), [97%Z; 98%Z; 99%Z].
    iSplitL "Habc_left"; [iExact "Habc_left"|].
    iSplitL "Habc_right"; [iExact "Habc_right"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_left Habc_right]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_half_split abc_addr Tuchar
      [97%Z; 98%Z; 99%Z]) with "[$Habc_left $Habc_right]") as "Habc".

    iPoseProof (object_bytesR_of_arrayLR abd_addr Tuchar (cQp.mk false 1)
      3 [97%Z; 98%Z; 100%Z] ltac:(reflexivity) with "Habd") as "Habd".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 100%Z].
    iSplitL "Habc"; [iExact "Habc"|].
    iSplitL "Habd"; [iExact "Habd"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc Habd]".
    Arith.arith_simpl.
    go.

    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 100%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z; 99%Z].
    iSplitL "Habd"; [iExact "Habd"|].
    iSplitL "Habc"; [iExact "Habc"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habd Habc]".
    Arith.arith_simpl.
    go.

    iPoseProof (object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habc")
      as "[Habc_prefix Habc_tail]".
    iPoseProof (object_bytesR_prefix_tail0 abd_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habd")
      as "[Habd_prefix Habd_tail]".
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z].
    iExists Tuchar, (cQp.mk false 1), [97%Z; 98%Z].
    iSplitL "Habc_prefix"; [iExact "Habc_prefix"|].
    iSplitL "Habd_prefix"; [iExact "Habd_prefix"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_prefix Habd_prefix]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habc_prefix $Habc_tail]") as "Habc".
    iPoseProof ((object_bytesR_prefix_tail0 abd_addr Tuchar
      (cQp.mk false 1) 2 3 [97%Z; 98%Z] [100%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habd_prefix $Habd_tail]") as "Habd".

    iPoseProof (object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 0 3 [] [97%Z; 98%Z; 99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Habc")
      as "[Habc_empty Habc]".
    iPoseProof (object_bytesR_of_arrayLR ab_addr Tuchar (cQp.mk false 1)
      2 [97%Z; 98%Z] ltac:(reflexivity) with "Hab") as "Hab".
    iPoseProof (object_bytesR_prefix_tail0 ab_addr Tuchar
      (cQp.mk false 1) 0 2 [] [97%Z; 98%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) with "Hab")
      as "[Hab_empty Hab]".
    iExists Tuchar, (cQp.mk false 1), [].
    iExists Tuchar, (cQp.mk false 1), [].
    iSplitL "Habc_empty"; [iExact "Habc_empty"|].
    iSplitL "Hab_empty"; [iExact "Hab_empty"|].
    iSplit; [done|].
    iSplit; [done|].
    iIntros "[Habc_empty Hab_empty]".
    Arith.arith_simpl.
    go.
    iPoseProof ((object_bytesR_prefix_tail0 abc_addr Tuchar
      (cQp.mk false 1) 0 3 [] [97%Z; 98%Z; 99%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Habc_empty $Habc]") as "Habc".
    iPoseProof ((object_bytesR_prefix_tail0 ab_addr Tuchar
      (cQp.mk false 1) 0 2 [] [97%Z; 98%Z]
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
      with "[$Hab_empty $Hab]") as "Hab".

    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 3%N
      [97%Z; 98%Z; 99%Z] ltac:(reflexivity) with "Habc") as "Habc".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 3%N
      [97%Z; 98%Z; 100%Z] ltac:(reflexivity) with "Habd") as "Habd".
    iPoseProof (object_bytesR_ucharR_arrayLR_anyR _ 1$m 2%N
      [97%Z; 98%Z] ltac:(reflexivity) with "Hab") as "Hab".
    iFrame "Habc Habd Hab".
    go.
  Qed.

  cpp.spec "test_memmove_overlap()" default.

  cpp.spec "test_cstring_slice4()" default.
  Lemma test_cstring_slice4_ok : verify[module] "test_cstring_slice4()".
  Proof. verify_spec; go. Qed.

End with_cpp.
