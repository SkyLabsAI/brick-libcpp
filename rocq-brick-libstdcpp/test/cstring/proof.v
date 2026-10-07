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

  Section with_resolve.
    Context {resolve:genv} (tu : translation_unit).
    Import operators.

    Lemma wp_eval_ptr_eq : forall ty ap bp (Q : val -> mpred),
        (∃ res, ptr_comparable ap bp res ** True //\\
          Q (Vbool res))
          |-- wp_eval_binop tu Beq (Tptr ty) (Tptr ty) Tbool (Vptr ap) (Vptr bp) Q.
    Proof.
      intros. iIntros "[%res HcmpQ]".
      rewrite wp_eval_binop.unlock !has_type_ptr' /eval_binop.
      iIntros "#? #?". iExists _.
      iSplit; last by iDestruct "HcmpQ" as "[_ $]".
      iPoseProof eval_ptr_eq as "H".
      iDestruct "HcmpQ" as "[Hcmp _]".
      iDestruct ("H" with "[Hcmp]") as "[$ $]".
      iDestruct "Hcmp" as "[$ _]".
    Qed.
    Definition wp_eval_ptr_eq_B := [BWD] wp_eval_ptr_eq.
  End with_resolve.
  Hint Resolve wp_eval_ptr_eq_B : sl_opacity.

  Section PtrIntoSub.
    Implicit Type (p : ptr) (o : offset) (os : list offset)
      (ty : type) (σ : genv) (i : Z) (f : field).
    Class PtrIntoSub (p1 p2 : ptr) ty i :=
      _ptr_into_sub : p1 = p2 .[ ty ! i ].
    #[global] Hint Mode PtrIntoSub + - - - : typeclass_instances sl_opacity.

    #[global] Instance PtrNorm_PtrIntoSub p1 p2 ty i :
      PtrNorm p1 (p2 .[ ty ! i]) ->
      PtrIntoSub p1 p2 ty i.
    Proof. by []. Qed.

    #[global] Instance PtrNorm_0_PtrIntoSub p1 p2 :
      PtrNorm p1 p2 ->
      PtrIntoSub p1 p2 "char" 0.
    Proof. rewrite /PtrIntoSub. normalize_ptrs. by []. Qed.
  End PtrIntoSub.
  (* Add Auto Subgoal PtrIntoSub. *)

  (* TODO upstream *)
  (* Extract from same_address_bool_partial_reflexive. *)
  Lemma same_address_partial_reflexive p :
    is_Some (ptr_vaddr p) ->
    same_address p p.
  Proof. by rewrite same_address_eq -same_property_reflexive_equiv. Qed.

  Lemma o_sub_eq_inj (p : ptr) ty i j sz :
    is_Some (ptr_vaddr (p .[ ty ! i ])) →
    size_of σ ty = Some sz → (0 < sz)%N →
    p .[ ty ! i ] = p .[ ty ! j ] <-> i = j.
  Proof.
    intros; split; last naive_solver; intros E.
    apply /(same_address_o_sub_eq p); [done|lia|].
    rewrite -{}E. exact /same_address_partial_reflexive.
  Qed.

  Lemma ptr_comparable_equiv p1 p2 res1 res2 :
    (is_Some (ptr_vaddr p1) -> is_Some (ptr_vaddr p2) -> res1 = res2) ->
    ptr_comparable p1 p2 res1 -|- ptr_comparable p1 p2 res2.
  Proof.
    rewrite ptr_comparable_eq /ptr_comparable_def !only_provable_wand_forall.
    intros Heq. f_equiv => -[Hp1 Hp2]. by move: Heq => /(_ Hp1 Hp2) ->.
  Qed.

  (* TODO: not obviously a bi-entailment, but could be if [ptr_comparable]'s
  definition were tweaked. *)
  Lemma ptr_ord_comparable_valid ty p1 p2 (p : ptr) (sz : N) (i j : Z) :
    size_of σ ty = Some sz →
    (0 < sz)%N →
    p1 = p .[ ty ! i ] →
    p2 = p .[ ty ! j ] →
    valid_ptr p1 ∗ valid_ptr p2 ⊢
    ptr_ord_comparable p1 p2 (λ va1 va2, bool_decide (va1 = va2)) (bool_decide (p1 = p2)).
  Proof.
    intros; subst.
    iApply (ptr_ord_comparable_off_off _ _ p) => //.
    intros va1 va2 Hva1 Hva2.
    vc_split (bool_decide (va1 = va2)) => Hva; simplify_eq; first last.
    all: case_bool_decide => //=. { congruence. }
    have /same_address_o_sub_eq Hij: same_address (p .[ ty ! i ]) (p .[ ty ! j ]).
    { exact /same_address_intro. }
    by odestruct (Hij sz); try lia.
  Qed.

  Lemma ptr_comparable_valid ty p1 p2 (p : ptr) (sz : N) (i j : Z) :
    size_of σ ty = Some sz →
    (0 < sz)%N →
    p1 = p .[ ty ! i ] →
    p2 = p .[ ty ! j ] →
    valid_ptr p1 ∗ valid_ptr p2 ⊢
    ptr_comparable p1 p2 (bool_decide (p1 = p2)).
  Proof. intros. rewrite -ptr_ord_comparable_comparable. exact: ptr_ord_comparable_valid. Qed.

  Lemma ptr_comparable_valid_idx ty p1 p2 (p : ptr) (sz : N) (i j : Z) :
    size_of σ ty = Some sz →
    (0 < sz)%N →
    p1 = p .[ ty ! i ] →
    p2 = p .[ ty ! j ] →
    valid_ptr p1 ∗ valid_ptr p2 ⊢
    ptr_comparable p1 p2 (bool_decide (i = j)).
  Proof.
    intros. rewrite ptr_comparable_equiv; first exact /ptr_comparable_valid.
    intros; subst; apply bool_decide_ext. rewrite o_sub_eq_inj //; lia.
  Qed.

  (* TODO review and upstream *)
  #[program]
  Definition ptr_comparable_valid_CX ty p1 p2 (p : ptr) sz (i j : Z) :=
    \cancelx
    \guard PtrIntoSub p1 p ty i
    \guard PtrIntoSub p2 p ty j
    \guard size_of σ ty = Some sz
    \guard StringSidecond (0 < sz)%N
    \through valid_ptr p1
    \through valid_ptr p2
    \whole_conclusion
    \bound Q res
    \proving (ptr_comparable p1 p2 res ** True) //\\ Q
    \through Q
    \through [| res = bool_decide (i = j) |]
    \end.
  Next Obligation. intros; work. rewrite -ptr_comparable_valid_idx //. work. Qed.
  Hint Resolve ptr_comparable_valid_CX : br_hints.

  cpp.spec "test_strchr()" from source default.
  Lemma test_strchr_ok : verify[source] "test_strchr()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_strrchr()" from source default.
  Lemma test_strrchr_ok : verify[source] "test_strrchr()".
  Proof.
    verify_spec; go.
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
  Qed.

  cpp.spec "test_strstr()" from source default.
  Lemma test_strstr_ok : verify[source] "test_strstr()".
  Proof.
    verify_spec; go.
  Qed.

  cpp.spec "test_cstring_slice1()" from source default.
  Lemma test_cstring_slice1_ok : verify[source] "test_cstring_slice1()".
  Proof. verify_spec; go. Qed.

End with_cpp.
