
(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.cstring.spec.
Require Export skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.test.existing_specs.cstring_cpp.

Import normalize.only_provable_norm.
Import normalize.normalize_ptr.
Import refine_lib.
Import expr_join.

#[local] Hint Resolve delayed_case.smash_delayed_case_B | 1000 : br_hints.
#[local] Hint Resolve delayed_case.expr_join.smash_delayed_case_B | 1000 : br_hints.

#[only(cfracsplittable)] derive cstring.R.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  cpp.spec "check_length_and_comparisons()" from source default.
  Lemma check_length_and_comparisons_ok :
    verify[source] "check_length_and_comparisons()".
  Proof. verify_spec; go $usenamed=true. Qed.

  (* Recovery-local bridge for literal char arrays.  It exposes the first
     null-terminated prefix as [cstring.R] and keeps the tail needed to
     reconstruct the original array after the library call. *)
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

  #[local] Lemma array_sliceR_cstring s tail q bytes m (p : ptr) :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    p |-> array_sliceR "char" 0 m (fun v : N => charR q v) bytes |--
    [| m = lengthZ bytes |] **
    p |-> cstring.R q s **
    p |-> array_sliceR "char" (m - lengthZ tail) m
            (fun v : N => charR q v) tail.
  Proof.
    work $usenamed=true.
    rewrite array_sliceR.unlock /cstring.R /zstring.R.
    work $usenamed=true.
    normalize_ptrs.
    by work $usenamed=true.
  Qed.

  #[local, program] Definition array_sliceR_open_cstring_C
      (p : ptr) q k bytes s tail
      (Hex : unpack_cstring bytes =[Vm]=> Some (s, tail)) :=
    \cancelx
    \consuming p |-> array_sliceR "char" 0 k (fun v : N => charR q v) bytes
    \bound qq ss
    \proving p |-> cstring.R qq ss
    \through [| qq = q |]
    \through [| ss = s |]
    \deduce p |-> array_sliceR "char" (k - lengthZ tail) k
                (fun v : N => charR q v) tail
    \end@{mpred}.
  Next Obligation.
    intros p q k bytes s tail Hs%RedEq_eq.
    pose proof (unpack_cstring_sound _ _ _ Hs) as [-> Hwf].
    work $usenamed=true.
    rewrite (array_sliceR_cstring _ []); [|by rewrite app_nil_r|done].
    work $usenamed=true.
  Qed.
  #[local] Hint Resolve array_sliceR_open_cstring_C : sl_opacity.

  #[local] Lemma replicateZ_lengthZ_eq_replicateN_lengthN {A} (xs : list A) :
    replicateZ (lengthZ xs) () = replicateN (lengthN xs) ().
  Proof. by rewrite /replicateZ N2Z.id. Qed.

  #[local] Lemma arrayR_charR_arrayR_anyR (p : ptr) q xs :
    p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs |--
    p |-> arrayR (Tchar_ char_type.Cchar)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite arrayR_anyR_f; last done.
    repeat f_equiv.
    rewrite length_lengthN repeatN_replicateN.
    by rewrite replicateZ_lengthZ_eq_replicateN_lengthN.
  Qed.

  #[local] Lemma array_sliceR_charR_array_sliceR_anyR (p : ptr) q xs :
    p |-> array_sliceR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun c : N => charR q c) xs |--
    p |-> array_sliceR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite array_sliceR.unlock.
    work $usenamed=true.
    rewrite arrayR_charR_arrayR_anyR.
    normalize_ptrs.
    work $usenamed=true.
  Qed.

  #[local] Lemma cstring_array_sliceR s tail q bytes m (p : ptr) :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    [| m = lengthZ bytes |] **
    p |-> cstring.R q s **
    p |-> array_sliceR "char" (m - lengthZ tail) m
            (fun v : N => charR q v) tail |--
    p |-> array_sliceR "char" 0 m (fun v : N => charR q v) bytes.
  Proof.
    intros -> Hwf; work $usenamed=true.
    rewrite lengthN_app.
    work $usenamed=true.
    rewrite array_sliceR.unlock /cstring.R /zstring.R.
    work $usenamed=true.
    by normalize_ptrs.
  Qed.

  #[local, program] Definition array_sliceR_close_cstring_C
      (p : ptr) q mid k tail s
      (Hmid : mid = lengthZ (cstring.to_zstring s))
      (Htailk : (mid = k - lengthZ tail)%Z) :=
    \cancelx
    \consuming p |-> cstring.R q s
    \consuming p |-> array_sliceR "char" mid k (fun v : N => charR q v) tail
    \proving p |-> array_sliceR "char" 0 k
         (fun _ : unit => anyR "char" q) (replicateZ k ())
    \end@{mpred}.
  Next Obligation.
    rewrite /cstring.R /zstring.R.
    intros.
    assert (k = lengthZ (cstring.to_zstring s ++ tail)) as ->.
    { rewrite lengthN_app. lia. }
    work $usenamed=true.
    iApply array_sliceR_charR_array_sliceR_anyR.
    iApply (cstring_array_sliceR s tail); first done.
    rewrite /cstring.R /zstring.R. work $usenamed=true.
  Qed.
  #[local] Hint Resolve array_sliceR_close_cstring_C : sl_opacity.

  cpp.spec "check_strchr_overloads()" from source default.
  Lemma check_strchr_overloads_ok :
    verify[source] "check_strchr_overloads()".
  Proof.

    verify_spec.

    go $usenamed=true.

    rewrite /cstring.R /zstring.R.

    go $usenamed=true.

    rewrite arrayR_eq /arrayR_def.

    rewrite arrR_eq /arrR_def.

    go $usenamed=true.

    rewrite big_sepL_cons.

    go $usenamed=true.

  Abort.

  cpp.spec "check_spans()" from source default.
  Lemma check_spans_ok : verify[source] "check_spans()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "check_memset()" from source default.
  Lemma check_memset_ok : verify[source] "check_memset()".
  Proof.

    verify_spec; go $usenamed=true.

    rewrite (array_sliceR_split' bytes_addr 0 3 4); [|lia|lia].

    go $usenamed=true.

  Abort.

  #[local] Lemma arrayR_ucharR_arrayR_anyR (p : ptr) q xs :
    p |-> arrayR "unsigned char" (fun c : Z => ucharR q c) xs |--
    p |-> arrayR "unsigned char"
           (fun _ : unit => anyR "unsigned char" q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite arrayR_anyR_f; last done.
    repeat f_equiv.
    rewrite length_lengthN repeatN_replicateN.
    by rewrite replicateZ_lengthZ_eq_replicateN_lengthN.
  Qed.

  #[local] Lemma array_sliceR_ucharR_array_sliceR_anyR (p : ptr) q xs :
    p |-> array_sliceR "unsigned char" 0 (lengthZ xs)
           (fun c : Z => ucharR q c) xs |--
    p |-> array_sliceR "unsigned char" 0 (lengthZ xs)
           (fun _ : unit => anyR "unsigned char" q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite array_sliceR.unlock.
    work $usenamed=true.
    rewrite arrayR_ucharR_arrayR_anyR.
    normalize_ptrs.
    work $usenamed=true.
  Qed.

  #[local, program] Definition array_sliceR_ucharR_anyR_C
      (p : ptr) q xs :=
    \cancelx
    \consuming p |-> array_sliceR "unsigned char" 0 (lengthZ xs)
          (fun c : Z => ucharR q c) xs
    \proving p |-> array_sliceR "unsigned char" 0 (lengthZ xs)
          (fun _ : unit => anyR "unsigned char" q)
          (replicateZ (lengthZ xs) ())
    \end@{mpred}.
  Next Obligation.
    intros p q xs.
    exact (array_sliceR_ucharR_array_sliceR_anyR p q xs).
  Qed.

  Lemma check_memset_ok : verify[source] "check_memset()".
  Proof.

    verify_spec; go $usenamed=true.

    rewrite (array_sliceR_split' bytes_addr 0 3 4); [|lia|lia].

    go $usenamed=true using array_sliceR_ucharR_anyR_C.

    iExists (replicateZ 3 ()).

    go $usenamed=true using array_sliceR_ucharR_anyR_C.
    all: exfalso.
    all: match goal with
         | Hlist : _ = [_] |- _ =>
             vm_compute in Hlist; congruence
         end.

  Qed.

  cpp.spec "check_memchr_overloads()" from source default.
  Lemma check_memchr_overloads_ok : verify[source] "check_memchr_overloads()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "check_memcmp()" from source default.
  Lemma check_memcmp_ok : verify[source] "check_memcmp()".
  Proof. verify_spec; go $usenamed=true. Qed.

  cpp.spec "check_memcpy()" from source default.
  Lemma check_memcpy_ok : verify[source] "check_memcpy()".
  Proof.

    verify_spec; go $usenamed=true.

    iExists (replicateZ 4 ()).

    go $usenamed=true using array_sliceR_ucharR_anyR_C.

  Qed.

  cpp.spec "check_memmove_nonoverlap()" from source default.
  Lemma check_memmove_nonoverlap_ok : verify[source] "check_memmove_nonoverlap()".
  Proof.
    verify_spec; go $usenamed=true.
    iExists (replicateZ 4 ()).
    go $usenamed=true using array_sliceR_ucharR_anyR_C.
  Qed.

  Lemma memmove_same_byte_overlap_unreachable (p : ptr) (b : Z) :
    p |-> ucharR (1 / 2)$c b **
    p |-> anyR "unsigned char" 1$m |-- False.
  Proof.

    work $usenamed=true.

  Abort.

  Lemma memmove_full_source_overlap_unreachable (p : ptr) (b : Z) :
    p |-> ucharR 1$c b **
    p |-> anyR "unsigned char" 1$m |-- False.
  Proof.
    rewrite primR_anyR.
    work $usenamed=true.
  Qed.

End with_cpp.
