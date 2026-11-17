(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.auto.cpp.linking_proof.
Require Import skylabs.brick.libstdcpp.immintrin.spec.
Require Import skylabs.brick.libstdcpp.test.immintrin.test_cpp.

Set Warnings "+sl-transparent-constants".
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C : db_skylabs_syntactic.

Definition is_control_byte (b : N) : bool :=
  bool_decide (b = 0x5b%N \/ (0x60 <= b <= 0x7f)%N).

Definition avx2_range_0x60_0x7f_bytes (bs : list N) : list N :=
  avx2_cmpgt_epi8 (avx2_set1_epi8 0xa0) (avx2_sub_epi8 bs (avx2_set1_epi8 0xe0)).

Definition control_mask_of_chunk32 (bs : list N) : N :=
  avx2_movemask_epi8
    (avx2_or_si256
       (avx2_cmpeq_epi8 bs (avx2_set1_epi8 0x5b))
       (avx2_range_0x60_0x7f_bytes bs)).

Definition chunk32 (b : nat) (bs : list N) : list N :=
  take 32 (drop (32 * b) bs).

Definition control_masks_of_bytes (nblocks : nat) (bs : list N) : list N :=
  (fun b => control_mask_of_chunk32 (chunk32 b bs)) <$> seq 0 nblocks.

Lemma vec256_wf_range_0x60_0x7f (bs : list N) :
  vec256_wf bs ->
  vec256_wf (avx2_range_0x60_0x7f_bytes bs).
Proof.
  intros Hwf.
  apply vec256_wf_cmpgt; [apply vec256_wf_set1 |].
  apply vec256_wf_sub; [exact Hwf | apply vec256_wf_set1].
Qed.

Lemma control_mask_of_chunk32_bound (bs : list N) :
  vec256_wf bs ->
  (control_mask_of_chunk32 bs < 2 ^ 32)%N.
Proof.
  intros Hwf.
  apply avx2_movemask_epi8_bound.
  apply vec256_wf_or.
  - apply vec256_wf_cmpeq; [exact Hwf | apply vec256_wf_set1].
  - exact (vec256_wf_range_0x60_0x7f bs Hwf).
Qed.

#[local] Hint Resolve
  vec256_wf_range_0x60_0x7f
  control_mask_of_chunk32_bound : pure sl_opacity has_type_prop.

Lemma control_mask_of_chunk32_bit_spec (bs : list N) (i : nat) :
  vec256_wf bs ->
  (i < 32)%nat ->
  N.testbit (control_mask_of_chunk32 bs) (N.of_nat i) =
  default false (is_control_byte <$> bs !! i).
Proof.
  intros [Hlen Hbounds] Hi.
  unfold control_mask_of_chunk32, avx2_range_0x60_0x7f_bytes.
  rewrite avx2_movemask_epi8_testbit.
  unfold avx2_or_si256, avx2_cmpeq_epi8, avx2_cmpgt_epi8, avx2_sub_epi8.
  rewrite !lookup_zip_with_gen.
  rewrite (avx2_set1_epi8_small 0x5b ltac:(lia)).
  rewrite (avx2_set1_epi8_small 0xa0 ltac:(lia)).
  rewrite (avx2_set1_epi8_small 0xe0 ltac:(lia)).
  rewrite (lookup_repeat_lt 0x5b%N 32 i Hi).
  rewrite (lookup_repeat_lt 0xa0%N 32 i Hi).
  rewrite (lookup_repeat_lt 0xe0%N 32 i Hi).
  destruct (lookup_lt_is_Some_2 bs i ltac:(lia)) as [op Hop].
  rewrite Hop /=.
  have Hop_lt : (op < 256)%N := Forall_lookup_1 _ _ _ _ Hbounds Hop.
  rewrite N.lor_spec.
  rewrite (avx2_signed_bias_range_0x60_0x7f op Hop_lt).
  unfold is_control_byte.
  case_bool_decide as Hjd; case_bool_decide as Hpush; simpl.
  - symmetry; apply bool_decide_eq_true_2; left; exact Hjd.
  - symmetry; apply bool_decide_eq_true_2; left; exact Hjd.
  - symmetry; apply bool_decide_eq_true_2; right; exact Hpush.
  - symmetry; apply bool_decide_eq_false_2; tauto.
Qed.

#[local] Lemma Forall_take {A : Type} (P : A -> Prop) (n : nat) (xs : list A) :
  List.Forall P xs ->
  List.Forall P (take n xs).
Proof.
  intros Hxs. revert n.
  induction Hxs as [|x xs Hx _ IH]; intros [|m]; simpl; constructor; auto.
Qed.

#[local] Lemma Forall_drop {A : Type} (P : A -> Prop) (n : nat) (xs : list A) :
  List.Forall P xs ->
  List.Forall P (drop n xs).
Proof.
  intros Hxs. revert n.
  induction Hxs as [|x xs Hx Hxs' IH]; intros [|m]; simpl.
  - constructor.
  - constructor.
  - constructor; [exact Hx | exact Hxs'].
  - apply IH.
Qed.

Lemma chunk32_wf (bs : list N) (nblocks b : nat) :
  length bs = (32 * nblocks)%nat ->
  List.Forall (fun x => (x < 256)%N) bs ->
  (b < nblocks)%nat ->
  vec256_wf (chunk32 b bs).
Proof.
  intros Hlen Hbounds Hb.
  unfold chunk32.
  split.
  - rewrite length_take length_drop Hlen. lia.
  - apply Forall_take, Forall_drop. exact Hbounds.
Qed.

Lemma control_masks_length (nblocks : nat) (bs : list N) :
  length (control_masks_of_bytes nblocks bs) = nblocks.
Proof.
  unfold control_masks_of_bytes.
  by rewrite length_fmap length_seq.
Qed.

Lemma control_masks_lookup (nblocks b : nat) (bs : list N) :
  (b < nblocks)%nat ->
  control_masks_of_bytes nblocks bs !! b =
  Some (control_mask_of_chunk32 (chunk32 b bs)).
Proof.
  intros Hb.
  unfold control_masks_of_bytes.
  rewrite list_lookup_fmap.
  rewrite (lookup_seq_lt 0 nblocks b Hb) /=.
  reflexivity.
Qed.

Theorem control_masks_global_bit_spec (bs : list N) (nblocks idx : nat) :
  length bs = (32 * nblocks)%nat ->
  List.Forall (fun x => (x < 256)%N) bs ->
  (idx < 32 * nblocks)%nat ->
  exists mask : N,
    control_masks_of_bytes nblocks bs !! (idx / 32)%nat = Some mask /\
    N.testbit mask (N.of_nat (idx mod 32)) =
      default false (is_control_byte <$> bs !! idx).
Proof.
  intros Hlen Hbounds Hidx.
  set (b := (idx / 32)%nat).
  set (r := (idx mod 32)%nat).
  have Hb : (b < nblocks)%nat by (subst b; apply Nat.Div0.div_lt_upper_bound; lia).
  have Hr : (r < 32)%nat by (subst r; apply Nat.mod_upper_bound; lia).
  exists (control_mask_of_chunk32 (chunk32 b bs)).
  split.
  - exact (control_masks_lookup nblocks b bs Hb).
  - rewrite (control_mask_of_chunk32_bit_spec (chunk32 b bs) r
               (chunk32_wf bs nblocks b Hlen Hbounds Hb) Hr).
    have -> : chunk32 b bs !! r = bs !! idx.
    { unfold chunk32.
      rewrite lookup_take_lt; [| exact Hr].
      rewrite lookup_drop.
      f_equal. subst b r.
      symmetry. exact (Nat.div_mod_eq idx 32). }
    reflexivity.
Qed.

#[local] Lemma list_split_chunk32 {A : Type} (xs : list A) (b : nat) :
  xs = take (32 * b) xs ++ take 32 (drop (32 * b) xs) ++ drop (32 * S b) xs.
Proof.
  rewrite -{1}(take_drop (32 * b) xs).
  f_equal.
  rewrite -{1}(take_drop 32 (drop (32 * b) xs)).
  f_equal.
  rewrite drop_drop.
  f_equal. lia.
Qed.

Local Opaque
  vec256_wf
  avx2_set1_epi8 avx2_cmpeq_epi8 avx2_sub_epi8 avx2_cmpgt_epi8
  avx2_or_si256 avx2_movemask_epi8
  control_mask_of_chunk32
  chunk32 control_masks_of_bytes.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} {MOD : source ⊧ σ}.

  Lemma code_arrayR_focus_chunk32 (code : ptr) (q : cQp.t) (bs : list N) (nblocks b : N) :
    length bs = (32 * N.to_nat nblocks)%nat ->
    (b < nblocks)%N ->
    code |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs) -|-
      code |-> arrayR Tuchar (primR Tuchar q) (Vn <$> take (32 * N.to_nat b) bs) **
      code .[ Tuchar ! Z.of_N (32 * b) ] |->
        arrayR Tuchar (primR Tuchar q) (Vn <$> chunk32 (N.to_nat b) bs) **
      code .[ Tuchar ! Z.of_N (32 * b + 32) ] |->
        arrayR Tuchar (primR Tuchar q) (Vn <$> drop (32 * S (N.to_nat b)) bs).
  Proof.
    intros Hlen Hb.
    rewrite {1}(list_split_chunk32 bs (N.to_nat b)).
    rewrite !fmap_app !arrayR_app !(_at_sep, _at_offsetR).
    have Hlen1 : Z.of_nat (length (Vn <$> take (32 * N.to_nat b) bs)) = Z.of_N (32 * b).
    { rewrite length_fmap length_take Hlen. lia. }
    have Hlen2 : Z.of_nat (length (Vn <$> chunk32 (N.to_nat b) bs)) = 32%Z.
    { Local Transparent chunk32. unfold chunk32.
      rewrite length_fmap length_take length_drop Hlen. lia. }
    rewrite Hlen1 Hlen2 o_sub_sub.
    replace (Z.of_N (32 * b) + 32)%Z with (Z.of_N (32 * b + 32)) by lia.
    by rewrite assoc.
  Qed.

  Lemma out_masks_uninit_step (out_masks : ptr) (nblocks b : N) :
    (b < nblocks)%N ->
    out_masks .[ Tuint ! Z.of_N b ] |->
      arrayR Tuint (fun _ : unit => anyR Tuint 1$m) (repeat tt (N.to_nat (nblocks - b))) |--
    out_masks .[ Tuint ! Z.of_N b ] |-> type_ptrR Tuint **
    out_masks .[ Tuint ! Z.of_N b ] |-> anyR Tuint 1$m **
    out_masks .[ Tuint ! Z.of_N (b + 1) ] |->
      arrayR Tuint (fun _ : unit => anyR Tuint 1$m) (repeat tt (N.to_nat (nblocks - (b + 1)))).
  Proof.
    intros Hb.
    replace (N.to_nat (nblocks - b)) with (S (N.to_nat (nblocks - (b + 1)))) by lia.
    simpl repeat.
    rewrite arrayR_cons !_at_sep _at_offsetR o_sub_sub.
    replace (Z.of_N b + 1)%Z with (Z.of_N (b + 1)) by lia.
    by rewrite assoc.
  Qed.

  Lemma out_masks_prefix_snoc (out_masks : ptr) (bs : list N) (nblocks b : N) :
    (b < nblocks)%N ->
    out_masks |-> arrayR Tuint (primR Tuint 1$m)
      (take (N.to_nat b) (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs)) **
    out_masks .[ Tuint ! Z.of_N b ] |->
      primR Tuint 1$m (Vn (control_mask_of_chunk32 (chunk32 (N.to_nat b) bs))) |--
    out_masks |-> arrayR Tuint (primR Tuint 1$m)
      (take (N.to_nat (b + 1)) (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs)).
  Proof.
    intros Hb.
    have Hlook :
      (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs) !! (N.to_nat b) =
      Some (Vn (control_mask_of_chunk32 (chunk32 (N.to_nat b) bs))).
    { rewrite list_lookup_fmap (control_masks_lookup (N.to_nat nblocks) (N.to_nat b) bs ltac:(lia)).
      reflexivity. }
    replace (N.to_nat (b + 1)) with (S (N.to_nat b)) by lia.
    rewrite (take_S_r _ _ _ Hlook).
    have Hlen :
      Z.of_nat (length (take (N.to_nat b) (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs))) =
      Z.of_N b.
    { rewrite length_take length_fmap control_masks_length. lia. }
    rewrite -Hlen.
    apply (arrayR_append' (primR Tuint 1$m) out_masks _ _ Tuint 4%N);
      [reflexivity | intros; apply _].
  Qed.

  cpp.spec "eq_bytes(__m256i, __m256i)" from source
    as eq_bytes_spec with (
      \arg{a : list N} "a" (Vvec a)
      \arg{b : list N} "b" (Vvec b)
      \require vec256_wf a
      \require vec256_wf b
      \post[Vvec (avx2_cmpeq_epi8 a b)] emp).

  cpp.spec "match_byte_mask_32(const uint8_t *, uint8_t)" from source
    as match_byte_mask_32_spec with (
      \arg{buf : ptr} "buf" (Vptr buf)
      \arg{needle : N} "needle" (Vn needle)
      \prepost{(q : cQp.t) (bs : list N)}
        buf |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs)
      \require vec256_wf bs
      \require (needle < 256)%N
      \post[Vn (avx2_movemask_epi8 (avx2_cmpeq_epi8 bs (avx2_set1_epi8 needle)))] emp).

  cpp.spec "range_0x60_0x7f_bytes(__m256i)" from source
    as range_0x60_0x7f_bytes_spec with (
      \arg{v : list N} "v" (Vvec v)
      \require vec256_wf v
      \post[Vvec (avx2_range_0x60_0x7f_bytes v)] emp).

  cpp.spec "control_mask_32(const uint8_t *)" from source
    as control_mask_32_spec with (
      \arg{buf : ptr} "buf" (Vptr buf)
      \prepost{(q : cQp.t) (bs : list N)}
        buf |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs)
      \require vec256_wf bs
      \post[Vn (control_mask_of_chunk32 bs)] emp).

  cpp.spec "scan_control_masks(const uint8_t *, size_t, uint32_t *)" from source
    as scan_control_masks_spec with (
      \arg{code : ptr} "code" (Vptr code)
      \arg{nblocks : N} "nblocks" (Vn nblocks)
      \arg{out_masks : ptr} "out_masks" (Vptr out_masks)
      \prepost{(q : cQp.t) (bs : list N)}
        code |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs)
      \pre out_masks |-> arrayR Tuint (fun _ : unit => anyR Tuint 1$m) (repeat tt (N.to_nat nblocks))
      \require length bs = (32 * N.to_nat nblocks)%nat
      \require List.Forall (fun b => (b < 256)%N) bs
      \require (nblocks < 2 ^ 55)%N
      \post out_masks |-> arrayR Tuint (primR Tuint 1$m)
        (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs)).

  Lemma eq_bytes_ok : verify[source] eq_bytes_spec.
  Proof using MOD.
    verify_spec.
    go.
  Qed.

  Lemma match_byte_mask_32_ok : verify[source] match_byte_mask_32_spec.
  Proof using MOD.
    verify_spec.
    go.
    iExists q, bs.
    go.
    rewrite N2Z.id.
    go.
    match goal with
    | Hwf : vec256_wf bs |- _ =>
        rewrite (to_unsigned_to_signed_W32 _
          (avx2_movemask_epi8_bound _
            (vec256_wf_cmpeq _ _ Hwf (vec256_wf_set1 needle))))
    end.
    go.
  Qed.

  Lemma range_0x60_0x7f_bytes_ok : verify[source] range_0x60_0x7f_bytes_spec.
  Proof using MOD.
    verify_spec.
    go.
  Qed.

  Lemma control_mask_32_ok : verify[source] control_mask_32_spec.
  Proof using MOD.
    verify_spec.
    go.
    iExists q, bs.
    go.
    Local Transparent control_mask_of_chunk32.
    unfold control_mask_of_chunk32.
    match goal with
    | Hwf : vec256_wf bs |- _ =>
        pose proof (control_mask_of_chunk32_bound bs Hwf) as Hbound
    end.
    unfold control_mask_of_chunk32 in Hbound.
    rewrite (to_unsigned_to_signed_W32 _ Hbound).
    Local Opaque control_mask_of_chunk32.
    go.
  Qed.

  Lemma scan_control_masks_ok : verify[source] scan_control_masks_spec.
  Proof using MOD.
    verify_spec.
    go.
    match goal with
    | Hlen0 : length bs = _ |- _ =>
        assert (length bs = (32 * N.to_nat nblocks)%nat) as Hlen by lia
    end.
    wp_while (fun ρ =>
      Exists cur : N,
        [| (cur <= nblocks)%N |] **
        _local ρ "code" |-> ptrR<Tuchar> 1$c code **
        _local ρ "nblocks" |-> ulongR 1$c (Z.of_N nblocks) **
        _local ρ "out_masks" |-> ptrR<Tuint> 1$c out_masks **
        _local ρ "b" |-> ulongR 1$m (Z.of_N cur) **
        code |-> arrayR Tuchar (primR Tuchar q) (Vn <$> bs) **
        out_masks |-> arrayR Tuint (primR Tuint 1$m)
          (take (N.to_nat cur) (Vn <$> control_masks_of_bytes (N.to_nat nblocks) bs)) **
        out_masks .[ Tuint ! Z.of_N cur ] |->
          arrayR Tuint (fun _ : unit => anyR Tuint 1$m) (repeat tt (N.to_nat (nblocks - cur)))).
    rewrite <- (bi.exist_intro 0%N).
    rewrite N.sub_0_r.
    simpl take.
    normalize_ptrs.
    go using _at_arrayR_nil_B.
    wp_if.
    {
      intros HltZ.
      match goal with
      | Hle : (?cur <= nblocks)%N, Hfb : List.Forall _ bs |- _ =>
          assert (cur < nblocks)%N as Hlt by lia;
          pose proof (chunk32_wf bs (N.to_nat nblocks) (N.to_nat cur) Hlen Hfb ltac:(lia)) as Hwf_chunk;
          pose proof (code_arrayR_focus_chunk32 code q bs nblocks cur Hlen Hlt) as Hfocus_lem;
          pose proof (out_masks_uninit_step out_masks nblocks cur Hlt) as Huninit_lem
      end.
      pose (Hfocus_F := [FWD->] Hfocus_lem).
      pose (Huninit_F := [FWD] Huninit_lem).
      go using Hfocus_F, Huninit_F.
      match goal with
      | Hlt : (?cur < nblocks)%N |- _ =>
          replace (32 * Z.of_N cur)%Z with (Z.of_N (32 * cur)) by lia;
          iExists q, (chunk32 (N.to_nat cur) bs)
      end.
      go.
      match goal with
      | Hlt : (?cur < nblocks)%N |- _ =>
          replace (Z.to_N (Z.of_N cur + 1)) with (cur + 1)%N by lia;
          pose proof (out_masks_prefix_snoc out_masks bs nblocks cur Hlt) as Hsnoc_lem
      end.
      pose (Hfocus_B := [BWD->] Hfocus_lem).
      pose (Hsnoc_B := [BWD] Hsnoc_lem).
      go using Hfocus_B, Hsnoc_B.
    }
    {
      intros HnltZ.
      match goal with
      | Hle : (?cur <= nblocks)%N |- _ =>
          assert (cur = nblocks) as -> by lia
      end.
      rewrite N.sub_diag.
      simpl repeat.
      rewrite take_ge; [| rewrite length_fmap control_masks_length; lia].
      go using _at_arrayR_nil_F.
    }
  Qed.

  Definition eq_bytes_ok_B := [LINK] eq_bytes_ok.
  Definition match_byte_mask_32_ok_B := [LINK] match_byte_mask_32_ok.
  Definition range_0x60_0x7f_bytes_ok_B := [LINK] range_0x60_0x7f_bytes_ok.
  Definition control_mask_32_ok_B := [LINK] control_mask_32_ok.
  Definition scan_control_masks_ok_B := [LINK] scan_control_masks_ok.
  #[local] Hint Resolve
    eq_bytes_ok_B
    match_byte_mask_32_ok_B
    range_0x60_0x7f_bytes_ok_B
    control_mask_32_ok_B
    scan_control_masks_ok_B : sl_opacity.

  Theorem immintrin_test_specs_ok :
    denoteModule source **
    mm256_loadu_si256_spec **
    mm256_set1_epi8_spec **
    mm256_cmpeq_epi8_spec **
    mm256_sub_epi8_spec **
    mm256_cmpgt_epi8_spec **
    mm256_or_si256_spec **
    mm256_movemask_epi8_spec
    |-- eq_bytes_spec **
        match_byte_mask_32_spec **
        range_0x60_0x7f_bytes_spec **
        control_mask_32_spec **
        scan_control_masks_spec.
  Proof using MOD.
    go.
  Qed.
End with_cpp.
