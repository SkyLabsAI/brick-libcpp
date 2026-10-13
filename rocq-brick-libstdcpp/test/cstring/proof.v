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
  Context `{Σ : cpp_logic} {σ:genv} . (*`{MOD : source ⊧ σ}.*)

  cpp.spec "test_strlen()" from source default.
  Lemma test_strlen_ok : verify[source] "test_strlen()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strcmp()" from source default.
  Lemma test_strcmp_ok : verify[source] "test_strcmp()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strncmp()" from source default.
  Lemma test_strncmp_ok : verify[source] "test_strncmp()".
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

  #[local] Lemma array_sliceR_cstring s tail q bytes m (p : ptr) :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    p |-> array_sliceR "char" 0 m (λ v : N, charR q v) bytes ⊢
    [| m = lengthZ bytes |] ∗
    p |-> cstring.R q s ∗
    p |-> array_sliceR "char" (m - lengthZ tail) m (λ v : N, charR q v) tail.
  Proof.
    work.
    rewrite array_sliceR.unlock /cstring.R /zstring.R.
    work.
    normalize_ptrs.
    by work.
  Qed.

  #[local, program] Definition array_sliceR_open_cstring_C
      (p : ptr) q k bytes s tail
      (Hex : unpack_cstring bytes =[Vm]=> Some (s, tail)) :=
    \cancelx
    \consuming p |-> array_sliceR "char" 0 k (λ v : N, charR q v) bytes
    \bound qq ss
    \proving p |-> cstring.R qq ss
    \through [| qq  = q |]
    \through [| ss = s |]
    \deduce p |-> array_sliceR "char" (k - lengthZ tail) k
                (λ v : N, charR q v) tail
    \end@{mpred}.
  Next Obligation.
    intros p q k bytes s tail Hs%RedEq_eq.
    pose proof (unpack_cstring_sound _ _ _ Hs) as [-> Hwf].
    work.
    rewrite (array_sliceR_cstring _ []); [ | by rewrite app_nil_r | done].
    work.
  Qed.
  #[local] Hint Resolve array_sliceR_open_cstring_C : sl_opacity.

  Lemma replicateZ_lengthZ_eq_replicateN_lengthN {A} (xs : list A) :
    replicateZ (lengthZ xs) () = replicateN (lengthN xs) ().
  Proof. by rewrite /replicateZ N2Z.id. Qed.

  Lemma arrayR_charR_arrayR_anyR (p : ptr) q xs :
    p |-> arrayR (Tchar_ char_type.Cchar) (fun c : N => charR q c) xs ⊢
    p |-> arrayR (Tchar_ char_type.Cchar)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite arrayR_anyR_f; last done.
    repeat f_equiv.
    rewrite length_lengthN repeatN_replicateN.
    by rewrite replicateZ_lengthZ_eq_replicateN_lengthN.
  Qed.

  Lemma array_sliceR_charR_array_sliceR_anyR  (p : ptr) q xs :
    p |-> array_sliceR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun c : N => charR q c) xs ⊢
    p |-> array_sliceR (Tchar_ char_type.Cchar) 0 (lengthZ xs)
           (fun _ : unit => anyR (Tchar_ char_type.Cchar) q)
           (replicateZ (lengthZ xs) ()).
  Proof.
    rewrite array_sliceR.unlock.
    work.
    rewrite arrayR_charR_arrayR_anyR.
    normalize_ptrs.
    work.
  Qed.

  #[local] Lemma cstring_array_sliceR s tail q bytes m (p : ptr) :
    bytes = cstring.to_zstring s ++ tail ->
    cstring.WF s ->
    [| m = lengthZ bytes |] ∗
    p |-> cstring.R q s ∗
    p |-> array_sliceR "char" (m - lengthZ tail) m (λ v : N, charR q v) tail ⊢
    p |-> array_sliceR "char" 0 m (λ v : N, charR q v) bytes.
  Proof.
    intros -> Hwf; work.
    rewrite lengthN_app.
    work.
    rewrite array_sliceR.unlock /cstring.R /zstring.R.
    work.
    by normalize_ptrs.
  Qed.

  #[local, program] Definition array_sliceR_close_cstring_C
      (p : ptr) q mid k tail s
      (Hmid : mid = lengthZ (cstring.to_zstring s))
      (Htailk : (mid = k - lengthZ tail)%Z) :=
    \cancelx
    \consuming p |-> cstring.R q s
    \consuming p |-> array_sliceR "char" mid k (λ v : N, charR q v) tail
    \proving p |-> array_sliceR "char" 0 k
         (λ _ : unit, anyR "char" q) (replicateZ k ())
    \end@{mpred}.
  Next Obligation.
    rewrite /cstring.R /zstring.R.
    intros.
    assert (k = lengthZ (cstring.to_zstring s ++ tail)) as ->.
    { rewrite lengthN_app. lia. }
    work.
    iApply array_sliceR_charR_array_sliceR_anyR.
    iApply (cstring_array_sliceR s tail); first done.
    rewrite /cstring.R /zstring.R. work.
  Qed.
  #[local] Hint Resolve array_sliceR_close_cstring_C : sl_opacity.

  cpp.spec "test_strlen_array_buffer()" from source default.
  Lemma test_strlen_array_buffer_ok :
    verify[source] "test_strlen_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strcmp_array_buffer()" from source default.
  Lemma test_strcmp_array_buffer_ok :
    verify[source] "test_strcmp_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strncmp_array_buffer()" from source default.
  Lemma test_strncmp_array_buffer_ok :
    verify[source] "test_strncmp_array_buffer()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strchr()" from source default.
  Lemma test_strchr_ok : verify[source] "test_strchr()".
  Proof.
    verify_spec; go.
    all: simpl in *; Arith.arith_simpl; normalize_ptrs; go.
    all: by exfalso.
  Qed.

  cpp.spec "test_strrchr()" from source default.
  Lemma test_strrchr_ok : verify[source] "test_strrchr()".
  Proof.
    verify_spec; go.
    all: simpl in *; Arith.arith_simpl; normalize_ptrs; go.
    all: by exfalso.
  Qed.

  cpp.spec "test_strspn()" from source default.
  Lemma test_strspn_ok : verify[source] "test_strspn()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strcspn()" from source default.
  Lemma test_strcspn_ok : verify[source] "test_strcspn()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_strpbrk()" from source default.
  Lemma test_strpbrk_ok : verify[source] "test_strpbrk()".
  Proof.
    verify_spec; go.
    all: Arith.arith_simpl; normalize_ptrs; go.
    all: by exfalso.
  Qed.

  cpp.spec "test_strstr()" from source default.
  Lemma test_strstr_ok : verify[source] "test_strstr()".
  Proof.
    verify_spec; go.
    all: Arith.arith_simpl; normalize_ptrs; go.
    all: by exfalso.
  Qed.

  cpp.spec "test_cstring_slice1()" from source default.
  Lemma test_cstring_slice1_ok : verify[source] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.

  (** * [mem*] clients *)

  (* TODO: some of this automation should be upstreamed, but it needs revisions and improvements for it. *)
  (** Stated on a plain [xs] so that [go] can use auto's [arrayR_entails_C];
      at the use sites below, [xs] is a [takeZ]/[dropZ] term and that hint's
      side condition [lengthZ xs = lengthZ ys] does not normalize to anything
      [go] can solve. *)
  Lemma array_sliceR_ucharR_anyR (p : ptr) m n q (xs : list Z) :
    p |-> array_sliceR Tuchar m n (λ b : Z, ucharR q b) xs ⊢
    p |-> array_sliceR Tuchar m n (λ _ : unit, anyR Tuchar q) (replicateZ (n - m) ()).
  Proof. go. Qed.

  (** The destination of [memset]/[memcpy]/[memmove] is a sub-slice of an
      initialized buffer, given up as [anyR]. *)
  #[local, program] Definition array_sliceR_ucharR_anyR_C
      (p : ptr) (m n m' n' : Z) (q : cQp.t) (xs : list Z)
      (_ : SolveArith (m <= m' <= n' /\ n' <= n)%Z) :=
    \cancelx
    \consuming p |-> array_sliceR Tuchar m n (λ b : Z, ucharR q b) xs
    \proving{(l : list unit)}
      p |-> array_sliceR Tuchar m' n' (λ _ : unit, anyR Tuchar q) l
    \through [| l = replicateZ (n' - m') () |]
    \deduce p |-> array_sliceR Tuchar m m' (λ b : Z, ucharR q b) (takeZ (m' - m) xs)
    \deduce p |-> array_sliceR Tuchar n' n (λ b : Z, ucharR q b)
                (dropZ (n' - m') (dropZ (m' - m) xs))
    \end@{mpred}.
  Next Obligation.
    intros * [Hb].
    rewrite (array_sliceR_split' p m m' n); [|lia..].
    rewrite (array_sliceR_split' p m' n' n); [|lia..].
    iIntros "($ & A & $)" (l ->).
    by iApply array_sliceR_ucharR_anyR.
  Qed.
  #[local] Hint Resolve array_sliceR_ucharR_anyR_C : sl_opacity.

  (** Returning a buffer whose first byte was split off. *)
  #[local, program] Definition array_sliceR_ucharR_cons_anyR_C
      (p : ptr) (n : Z) (q : cQp.t) (x : Z) (xs : list Z) :=
    \cancelx
    \consuming p |-> ucharR q x
    \consuming p |-> array_sliceR Tuchar 1 n (λ b : Z, ucharR q b) xs
    \proving{(l : list unit)}
      p |-> array_sliceR Tuchar 0 n (λ _ : unit, anyR Tuchar q) l
    \through [| l = replicateZ n () |]
    \end@{mpred}.
  Next Obligation.
    intros. iIntros "[X XS]" (l ->).
    rewrite -[n in replicateZ n](Z.sub_0_r n).
    iApply (array_sliceR_ucharR_anyR p 0 n q (x :: xs)).
    rewrite array_sliceR_cons offset_ptr_sub_0 //. iFrame "XS".
    iDestruct (observe (type_ptr Tuchar p) with "X") as "#$". iFrame.
  Qed.
  #[local] Hint Resolve array_sliceR_ucharR_cons_anyR_C : sl_opacity.

  (** Evaluate closed applications of the [cstring] model functions. *)
  #[local] Ltac is_model t :=
    lazymatch t with
    | memchr _ _ => idtac | memcmp _ _ => idtac | memset _ _ => idtac
    | byte_of_int _ => idtac | dropZ _ _ => idtac | takeZ _ _ => idtac
    | replicateZ _ _ => idtac
    end.
  (* TODO: reuse skylabs.auto.closed. *)
  #[local] Ltac closed t :=
    match t with context [?v] => is_var v; fail 1 | _ => idtac end.
  #[local] Ltac compute_model :=
    repeat match goal with
    | |- context [?t] =>
        is_model t; closed t;
        let v := eval vm_compute in t in progress change t with v
    | H : context [?t] |- _ =>
        is_model t; closed t;
        let v := eval vm_compute in t in progress change t with v in H
    end.

  (** Destruct a list variable whose length is a known literal. *)
  #[local] Ltac destruct_sized_list :=
    match goal with
    | H : list.ListSizeZ ?xs ?n |- _ =>
        is_var xs; closed n;
        (* TODO: this OOMs unnecessarily on large lists *)
        let k := eval vm_compute in (Z.to_nat n) in
        let Hl := fresh "Hl" in
        assert (Hl : length xs = k)
          by (apply list.ListSizeZ_iff in H; rewrite lengthZ_correct in H; lia);
        clear H;
        repeat (destruct xs as [|? xs];
                [first [discriminate Hl | clear Hl]
                |first [discriminate Hl | injection Hl as Hl]])
    end.

  (** [go] stops at model computations, list shapes, and the unconstrained
      [unit]/fraction witnesses of (empty) slices. *)
  #[local] Ltac finish :=
    repeat (first [progress compute_model | progress destruct_sized_list
                  | progress simplify_eq/= | iExists () | iExists 1%cQp
                  | progress normalize_ptrs]; go).

  cpp.spec "test_memchr()" from source default.
  Lemma test_memchr_ok : verify[source] "test_memchr()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memchr_embedded_null()" from source default.
  Lemma test_memchr_embedded_null_ok : verify[source] "test_memchr_embedded_null()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memcmp()" from source default.
  Lemma test_memcmp_ok : verify[source] "test_memcmp()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memcmp_embedded_null()" from source default.
  Lemma test_memcmp_embedded_null_ok : verify[source] "test_memcmp_embedded_null()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memset()" from source default.
  Lemma test_memset_ok : verify[source] "test_memset()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memset_embedded_null()" from source default.
  Lemma test_memset_embedded_null_ok : verify[source] "test_memset_embedded_null()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memcpy()" from source default.
  Lemma test_memcpy_ok : verify[source] "test_memcpy()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memcpy_embedded_null()" from source default.
  Lemma test_memcpy_embedded_null_ok : verify[source] "test_memcpy_embedded_null()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_memmove()" from source default.
  Lemma test_memmove_ok : verify[source] "test_memmove()".
  Proof. verify_spec; go; finish. Qed.

  (* [test_memmove_overlap()] and [test_memmove_embedded_null()] are out of
     reach: the [memmove] spec requires disjoint [unsigned char] buffers. *)

  cpp.spec "test_cstring_slice4()" from source default.
  Lemma test_cstring_slice4_ok : verify[source] "test_cstring_slice4()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_mem_zero_length()" from source default.
  Lemma test_mem_zero_length_ok : verify[source] "test_mem_zero_length()".
  Proof. verify_spec; go; finish. Qed.

  cpp.spec "test_search_embedded_null_array_buffer()" from source default.
  Lemma test_search_embedded_null_array_buffer_ok :
    verify[source] "test_search_embedded_null_array_buffer()".
  Proof. verify_spec; go; finish. Qed.

End with_cpp.
