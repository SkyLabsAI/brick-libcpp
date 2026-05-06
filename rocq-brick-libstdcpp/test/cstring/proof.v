(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Export skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.test.cstring.test_cpp.

Import normalize.only_provable_norm.
Import normalize.normalize_ptr.
Import refine_lib.
Import expr_join.

#[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
#[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.

#[only(cfracsplittable)] derive cstring.R. (*Upstream into auto*)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ:genv} . (*`{MOD : module ⊧ σ}.*)

  cpp.spec "test_strlen()" from module default.
  Lemma test_strlen_ok : verify[module] "test_strlen()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strcmp()" from module default.
  Lemma test_strcmp_ok : verify[module] "test_strcmp()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strncmp()" from module default.
  Lemma test_strncmp_ok : verify[module] "test_strncmp()".
  Proof. verify_spec; go. Qed.

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

  (* Currently dead but provable lemmas
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

  #[local] Lemma arrayLR_cstring q bytes m tail (p : ptr) s :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    p |-> arrayLR "char" 0 m (λ v : N, charR q v) bytes ⊢
    [| m = lengthZ bytes |] ∗
    p |-> cstring.R q s ∗
    p |-> arrayLR "char" (m - lengthZ tail) m (λ v : N, charR q v) tail.
  Proof.
    intros -> Hwf; work.
    rewrite arrayLR.unlock _at_sep.
    arith_simpl; work.
    rewrite _at_sub_0; [|done].
    rewrite /cstring.R /zstring.R; iFrame; done.
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
    intros -> Hwf; work.
    rewrite lengthN_app; arith_simpl.
    rewrite /cstring.R /zstring.R; work.
    rewrite arrayLR.unlock; arith_simpl; work.
    rewrite _at_sub_0; [trivial|done].
  Qed.
  Hint Resolve cstring_arrayLR : sl_opacity.

  #[local, program] Definition arrayLR_open_cstring_C
      (p : ptr) q k bytes s tail
      (Hex : unpack_cstring bytes =[Vm]=> Some (s, tail)) :=
    \cancelx
    \consuming p |-> arrayLR "char" 0 k (λ v : N, charR q v) bytes
    \bound qq ss
    \proving p |-> cstring.R qq ss
    \through [| qq  = q |]
    \through [| ss = s |]
    \deduce p |-> arrayLR "char" (k - lengthZ tail) k
                (λ v : N, charR q v) tail
    \end@{mpred}.
  Next Obligation.
    intros p q k bytes s tail Hs%RedEq_eq.
    pose proof (unpack_cstring_sound _ _ _ Hs) as [Hbytes0 Hwf0]. work.
    rewrite arrayLR_cstring . work. by rewrite app_nil_r. done.
  Qed.
  #[local] Hint Resolve arrayLR_open_cstring_C : sl_opacity.

  Lemma at_charR_anyR (p : ptr) q x :
    p |-> charR q x ⊢ p |-> anyR (Tchar_ char_type.Cchar) q.
  Proof.
    apply heap_pred._at_cancel.
    apply primR_anyR.
  Qed.

  Lemma replicateZ_lengthZ_eq_replicateN_lengthN {A : Type} (xs : list A) (x : unit) :
    replicateZ (lengthZ xs) x = replicateN (lengthN xs) x.
  Proof.
    by rewrite /replicateZ N2Z.id.
  Qed.

  Lemma arrayR_charR_arrayR_anyR (p : ptr) q xs :
    p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
    p |-> arrayR (Tchar_ char_type.Cchar)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    revert p.
    induction xs as [|x xs IH].
    all: intros p.
    - rewrite /replicateZ N2Z.id /= !arrayR_nil. reflexivity.
    - rewrite arrayR_cons !_at_sep _at_offsetR.
      iIntros "(Hty & Hx & Hxs)".
      replace (replicateZ (lengthZ (x :: xs)) ()) with
        (() :: replicateZ (lengthZ xs) ()).
      2:{
        rewrite !replicateZ_lengthZ_eq_replicateN_lengthN.
        rewrite /lengthN Nat2N.inj_succ replicateN_S.
        reflexivity.
      }
      rewrite arrayR_cons !_at_sep _at_offsetR.
      iFrame "Hty".
      iSplitL "Hx".
      + iApply (at_charR_anyR with "Hx").
      + iApply (IH with "Hxs").
  Qed.

  Lemma arrayLR_charR_arrayLR_anyR  (p : ptr) q xs :
    p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun c : N => charR q c) xs ⊢
    p |-> arrayLR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite arrayLR.unlock _at_sep.
    iIntros "[_ Harr]".
    rewrite _at_offsetR _at_sub_0; [|done].
    iPoseProof (arrayR_charR_arrayR_anyR _ q with "Harr") as "Harr".
    rewrite /arrayLR.
    iSplit.
    - iPureIntro.
      rewrite replicateZ_lengthZ_eq_replicateN_lengthN.
      unfold lengthN, replicateN.
      rewrite length_replicate.
      rewrite Nat2N.id.
      lia.
    - rewrite _at_offsetR _at_sub_0; [|done].
      iExact "Harr".
  Qed.

  #[local, program] Definition arrayLR_close_cstring_C
      (p : ptr) q mid k tail s
      (Hmid : mid = lengthZ (cstring.to_zstring s))
      (Htailk : (mid = k - lengthZ tail)%Z) :=
    \cancelx
    \consuming p |-> cstring.R q s
    \consuming p |-> arrayLR "char" mid k (λ v : N, charR q v) tail
    \proving p |-> arrayLR "char" 0 k
         (λ _ : unit, anyR "char" q) (replicateZ k ())
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
    rewrite Hk.
    iPoseProof (arrayLR_charR_arrayLR_anyR _ q (cstring.to_zstring s ++ tail)
      with "Harr") as "Harr".
    iExact "Harr".
  Qed.
  #[local] Hint Resolve arrayLR_close_cstring_C : sl_opacity.

  #[local] Lemma char_ptr_sub_0 (p : ptr) :
    p.[ "char" ! 0 ] = p.
  Proof.
    assert (Hsz : is_Some (size_of σ "char")) by (vm_compute; eauto).
    exact (offset_ptr_sub_0 p "char" Hsz).
  Qed.

  cpp.spec "test_strlen_array_buffer()" from module default.
  Lemma test_strlen_array_buffer_ok :
    verify[module] "test_strlen_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strcmp_array_buffer()" from module default.
  Lemma test_strcmp_array_buffer_ok :
    verify[module] "test_strcmp_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strncmp_array_buffer()" from module default.
  Lemma test_strncmp_array_buffer_ok :
    verify[module] "test_strncmp_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strchr()" from module default.
  Lemma test_strchr_ok : verify[module] "test_strchr()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    Arith.arith_simpl; go.
    normalize_ptrs.
    Arith.arith_simpl.
    - contradiction.
    - rewrite char_ptr_sub_0 in H. contradiction.
  Qed.

  cpp.spec "test_strrchr()" from module default.
  Lemma test_strrchr_ok : verify[module] "test_strrchr()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    Arith.arith_simpl; go.
    normalize_ptrs.
    Arith.arith_simpl.
    - contradiction.
    - rewrite char_ptr_sub_0 in H. contradiction.
  Qed.

  cpp.spec "test_strspn()" from module default.
  Lemma test_strspn_ok : verify[module] "test_strspn()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strcspn()" from module default.
  Lemma test_strcspn_ok : verify[module] "test_strcspn()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strpbrk()" from module default.
  Lemma test_strpbrk_ok : verify[module] "test_strpbrk()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    Arith.arith_simpl.
    contradiction.
  Qed.

  cpp.spec "test_strstr()" from module default.
  Lemma test_strstr_ok : verify[module] "test_strstr()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    Arith.arith_simpl; go.
    normalize_ptrs.
    Arith.arith_simpl.
    - contradiction.
    - rewrite char_ptr_sub_0 in H. contradiction.
  Qed.

  cpp.spec "test_cstring_slice1()" from module default.
  Lemma test_cstring_slice1_ok : verify[module] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.

End with_cpp.
