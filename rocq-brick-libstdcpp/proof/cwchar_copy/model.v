
(*
 * Operational reference model for the selected C++20 <cwchar> copy,
 * concatenation, fill, and collation functions.  It was authored from
 * C++20 [cwchar.syn], ISO C N1570 7.29.4.2--7.29.4.4 and 7.29.4.6.2,
 * cppreference, and the public <cwchar>/<wchar.h> declarations, without a
 * synthesized specification.
 *
 * A [wide_memory] is one flat allocation and a [pointer] is a Z offset into
 * it.  This makes overlap and unchanged framing observable.  [None] denotes
 * a call outside the standard-defined domain.  The locale's LC_COLLATE state
 * is represented explicitly by a transformation from source payloads to
 * transformed payloads; terminating nulls are not stored in either payload.
 *)
From Stdlib Require Import List ZArith Bool.
Import ListNotations.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.

Definition wchar := Z.
Definition pointer := Z.
Definition wide_memory := list wchar.
Definition collation := list wchar -> list wchar.
Definition mutation_result := (pointer * wide_memory)%type.
Definition transform_result := (Z * wide_memory)%type.

Definition lengthZ {A : Type} (xs : list A) : Z :=
  Z.of_nat (List.length xs).

Definition valid_pointerb (memory : wide_memory) (p : pointer) : bool :=
  Z.leb 0 p && Z.leb p (lengthZ memory).

Definition range_okb
    (memory : wide_memory) (start count : Z) : bool :=
  Z.leb 0 start && Z.leb 0 count &&
  Z.leb (start + count) (lengthZ memory).

Definition range_values
    (memory : wide_memory) (start count : Z) : wide_memory :=
  firstn (Z.to_nat count) (skipn (Z.to_nat start) memory).

Definition replace_range
    (memory : wide_memory) (start : Z) (values : wide_memory)
    : wide_memory :=
  firstn (Z.to_nat start) memory ++ values ++
  skipn (Z.to_nat start + List.length values) memory.

Definition ranges_disjointb
    (p n q m : Z) : bool :=
  Z.leb (p + n) q || Z.leb (q + m) p.

Fixpoint payload_before_nul (xs : wide_memory) : option wide_memory :=
  match xs with
  | [] => None
  | x :: tail =>
      if Z.eqb x 0
      then Some []
      else option_map (cons x) (payload_before_nul tail)
  end.

Definition string_payload_at
    (memory : wide_memory) (p : pointer) : option wide_memory :=
  if valid_pointerb memory p
  then payload_before_nul (skipn (Z.to_nat p) memory)
  else None.

Definition string_extent (payload : wide_memory) : Z :=
  lengthZ payload + 1.

Fixpoint bounded_payload
    (fuel : nat) (xs : wide_memory) : option (wide_memory * bool) :=
  match fuel with
  | O => Some ([], false)
  | S fuel' =>
      match xs with
      | [] => None
      | x :: tail =>
          if Z.eqb x 0
          then Some ([], true)
          else
            match bounded_payload fuel' tail with
            | Some (payload, terminated) => Some (x :: payload, terminated)
            | None => None
            end
      end
  end.

Definition bounded_payload_at
    (memory : wide_memory) (p count : Z)
    : option (wide_memory * bool) :=
  if valid_pointerb memory p && Z.leb 0 count
  then bounded_payload (Z.to_nat count) (skipn (Z.to_nat p) memory)
  else None.

Definition bounded_read_extent
    (payload : wide_memory) (terminated : bool) : Z :=
  lengthZ payload + if terminated then 1 else 0.

Definition strncpy_output
    (count : Z) (payload : wide_memory) (terminated : bool)
    : wide_memory :=
  if terminated
  then payload ++ List.repeat 0 (Z.to_nat count - List.length payload)
  else payload.

Definition wcscpy
    (memory : wide_memory) (dest src : pointer)
    : option mutation_result :=
  match string_payload_at memory src with
  | None => None
  | Some payload =>
      let copied := payload ++ [0] in
      let extent := lengthZ copied in
      if range_okb memory dest extent &&
         ranges_disjointb dest extent src extent
      then Some (dest, replace_range memory dest copied)
      else None
  end.

Definition wcsncpy
    (memory : wide_memory) (dest src count : Z)
    : option mutation_result :=
  match bounded_payload_at memory src count with
  | None => None
  | Some (payload, terminated) =>
      let consumed := bounded_read_extent payload terminated in
      let copied := strncpy_output count payload terminated in
      if range_okb memory dest count &&
         ranges_disjointb dest count src consumed
      then Some (dest, replace_range memory dest copied)
      else None
  end.

Definition wcscat
    (memory : wide_memory) (dest src : pointer)
    : option mutation_result :=
  match string_payload_at memory dest, string_payload_at memory src with
  | Some dest_payload, Some src_payload =>
      let copied := src_payload ++ [0] in
      let result_extent := lengthZ dest_payload + lengthZ copied in
      let src_extent := lengthZ copied in
      if range_okb memory dest result_extent &&
         ranges_disjointb dest result_extent src src_extent
      then
        Some (dest,
          replace_range memory (dest + lengthZ dest_payload) copied)
      else None
  | _, _ => None
  end.
Definition wcsncat
    (memory : wide_memory) (dest src count : Z)
    : option mutation_result :=
  match string_payload_at memory dest,
        bounded_payload_at memory src count with
  | Some dest_payload, Some (src_payload, terminated) =>
      let consumed := bounded_read_extent src_payload terminated in
      let appended := src_payload ++ [0] in
      let result_extent := lengthZ dest_payload + lengthZ appended in
      if range_okb memory dest result_extent &&
         ranges_disjointb dest result_extent src consumed
      then
        Some (dest,
          replace_range memory (dest + lengthZ dest_payload) appended)
      else None
  | _, _ => None
  end.



Definition wmemcpy
    (memory : wide_memory) (dest src count : Z)
    : option mutation_result :=
  if range_okb memory dest count && range_okb memory src count &&
     ranges_disjointb dest count src count
  then
    Some (dest,
      replace_range memory dest (range_values memory src count))
  else None.

Definition wmemmove
    (memory : wide_memory) (dest src count : Z)
    : option mutation_result :=
  if range_okb memory dest count && range_okb memory src count
  then
    (* [range_values] is evaluated on the pre-state, modeling the temporary. *)
    Some (dest,
      replace_range memory dest (range_values memory src count))
  else None.

Definition wmemset
    (memory : wide_memory) (dest value count : Z)
    : option mutation_result :=
  if range_okb memory dest count
  then
    Some (dest,
      replace_range memory dest (List.repeat value (Z.to_nat count)))
  else None.

Definition compare_wchar (x y : wchar) : Z :=
  if Z.ltb x y then -1 else if Z.ltb y x then 1 else 0.

Fixpoint compare_payloads (lhs rhs : wide_memory) : Z :=
  match lhs, rhs with
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
      let order := compare_wchar x y in
      if Z.eqb order 0 then compare_payloads xs ys else order
  end.

Definition wcscoll
    (locale : collation) (lhs rhs : wide_memory) : option Z :=
  match string_payload_at lhs 0, string_payload_at rhs 0 with
  | Some lhs_payload, Some rhs_payload =>
      Some (compare_payloads (locale lhs_payload) (locale rhs_payload))
  | _, _ => None
  end.

Definition xfrm_destination_okb
    (memory : wide_memory) (dest : option pointer)
    (src source_extent count : Z) : bool :=
  if Z.eqb count 0
  then
    match dest with
    | None => true
    | Some p => valid_pointerb memory p
    end
  else
    match dest with
    | None => false
    | Some p =>
        range_okb memory p count &&
        ranges_disjointb p count src source_extent
    end.

Definition wcsxfrm
    (locale : collation) (memory : wide_memory)
    (dest : option pointer) (src count : Z)
    : option transform_result :=
  match string_payload_at memory src with
  | None => None
  | Some source =>
      let key := locale source in
      let result := lengthZ key in
      let source_extent := string_extent source in
      if Z.leb 0 count &&
         xfrm_destination_okb memory dest src source_extent count
      then
        if Z.eqb count 0
        then Some (result, memory)
        else
          match dest with
          | None => None
          | Some p =>
              if Z.ltb result count
              then Some (result, replace_range memory p (key ++ [0]))
              else
                (* One conforming witness for indeterminate destination data. *)
                Some (result,
                  replace_range memory p
                    (firstn (Z.to_nat count) (key ++ [0])))
          end
      else None
  end.

(* The relational form records the standard's weaker insufficient-buffer
   guarantee: when [result >= count], any [count] destination values are a
   conforming post-state. *)
Definition wcsxfrm_step
    (locale : collation) (before : wide_memory)
    (dest : option pointer) (src count result : Z)
    (after : wide_memory) : Prop :=
  exists source,
    string_payload_at before src = Some source /\
    0 <= count /\
    xfrm_destination_okb before dest src (string_extent source) count = true /\
    result = lengthZ (locale source) /\
    if Z.eqb count 0
    then after = before
    else
      match dest with
      | None => False
      | Some p =>
          if Z.ltb result count
          then after = replace_range before p (locale source ++ [0])
          else exists values,
              List.length values = Z.to_nat count /\
              after = replace_range before p values
      end.

Definition reverse_collation : collation := fun xs => List.rev xs.

(* --- realizability and adversarial boundary witnesses --- *)
Example wcscpy_copies_terminator_and_returns_destination :
  wcscpy [65; 66; 0; 9; 8; 7; 6] 4 0 =
    Some (4, [65; 66; 0; 9; 65; 66; 0]).
Proof. vm_compute; reflexivity. Qed.

Example wcsncpy_padding_and_nontermination_are_realizable :
  wcsncpy [65; 0; 9; 8; 7; 6; 5; 4] 3 0 4 =
    Some (3, [65; 0; 9; 65; 0; 0; 0; 4]) /\
  wcsncpy [65; 66; 67; 9; 8; 7] 4 0 2 =
    Some (4, [65; 66; 67; 9; 65; 66]).
Proof. vm_compute; split; reflexivity. Qed.

Example concatenation_boundaries_are_realizable :
  wcscat [65; 0; 9; 8; 7; 6; 66; 67; 0; 5] 0 6 =
    Some (0, [65; 66; 67; 0; 7; 6; 66; 67; 0; 5]) /\
  wcsncat [65; 0; 9; 8; 7; 6; 66; 67; 68; 0; 5] 0 6 2 =
    Some (0, [65; 66; 67; 0; 7; 6; 66; 67; 68; 0; 5]).
Proof. vm_compute; split; reflexivity. Qed.

Example memcpy_rejects_overlap_while_memmove_uses_a_snapshot :
  wmemcpy [1; 2; 3; 4; 5] 1 0 4 = None /\
  wmemmove [1; 2; 3; 4; 5] 1 0 4 =
    Some (1, [1; 1; 2; 3; 4]) /\
  wmemmove [1; 2; 3; 4; 5] 0 1 4 =
    Some (0, [2; 3; 4; 5; 5]).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example counted_zero_calls_do_nothing :
  wcsncpy [1] 0 0 0 = Some (0, [1]) /\
  wcsncat [65; 0; 9; 66; 0] 0 3 0 =
    Some (0, [65; 0; 9; 66; 0]) /\
  wmemcpy [1] 0 0 0 = Some (0, [1]) /\
  wmemmove [1] 0 0 0 = Some (0, [1]) /\
  wmemset [1] 0 9 0 = Some (0, [1]).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example locale_order_and_transform_are_realizable :
  wcscoll reverse_collation [1; 2; 0] [2; 1; 0] = Some 1 /\
  wcsxfrm reverse_collation [1; 2; 0; 9; 8; 7; 6; 5]
    (Some 4) 0 3 = Some (2, [1; 2; 0; 9; 2; 1; 0; 5]) /\
  wcsxfrm reverse_collation [1; 2; 0] None 0 0 =
    Some (2, [1; 2; 0]).
Proof. vm_compute; repeat split; reflexivity. Qed.

Example insufficient_transform_contents_are_not_fixed :
  wcsxfrm_step reverse_collation
    [1; 2; 0; 9; 8; 7] (Some 4) 0 2 2 [1; 2; 0; 9; 44; 55].
Proof.
  exists [1; 2].
  vm_compute.
  repeat split; try reflexivity.
  discriminate.
exists [44; 55].
  split; reflexivity.

Qed.

(** A public model of the active [LC_COLLATE] transformation.  Its key never
    contains an embedded null when the source payload does not. *)
Record locale_model : Type := {
  locale_transform : collation;
  locale_transform_wf : forall source,
    Forall (fun x => x <> 0) source ->
    Forall (fun x => x <> 0) (locale_transform source)
}.

(** Proposition-level standard domains used by the public specifications. *)
Definition valid_pointer
    (memory : wide_memory) (p : pointer) : Prop :=
  0 <= p <= lengthZ memory.

Definition readable_range
    (memory : wide_memory) (p count : Z) : Prop :=
  0 <= p /\ 0 <= count /\ p + count <= lengthZ memory.

Definition disjoint_ranges (p n q m : Z) : Prop :=
  p + n <= q \/ q + m <= p.

Definition string_at
    (memory : wide_memory) (p : pointer) (payload : wide_memory) : Prop :=
  exists suffix,
    valid_pointer memory p /\
    skipn (Z.to_nat p) memory = payload ++ 0 :: suffix /\
    Forall (fun x => x <> 0) payload.

Definition bounded_source_at
    (memory : wide_memory) (p count : Z)
    (payload : wide_memory) (read_extent : Z) : Prop :=
  (0 <= count /\
   lengthZ payload = count /\
   readable_range memory p count /\
   payload = firstn (Z.to_nat count) (skipn (Z.to_nat p) memory) /\
   Forall (fun x => x <> 0) payload /\
   read_extent = count) \/
  (exists suffix,
    0 <= count /\
    lengthZ payload < count /\
    valid_pointer memory p /\
    skipn (Z.to_nat p) memory = payload ++ 0 :: suffix /\
    Forall (fun x => x <> 0) payload /\
    read_extent = lengthZ payload + 1).

Definition wcscpy_callable
    (memory : wide_memory) (dest src : pointer) : Prop :=
  exists source,
    string_at memory src source /\
    readable_range memory dest (lengthZ source + 1) /\
    disjoint_ranges dest (lengthZ source + 1)
                    src (lengthZ source + 1).

Definition wcsncpy_callable
    (memory : wide_memory) (dest src count : Z) : Prop :=
  exists source read_extent,
    bounded_source_at memory src count source read_extent /\
    readable_range memory dest count /\
    disjoint_ranges dest count src read_extent.

Definition wcscat_callable
    (memory : wide_memory) (dest src : pointer) : Prop :=
  exists old source,
    string_at memory dest old /\
    string_at memory src source /\
    readable_range memory dest (lengthZ old + lengthZ source + 1) /\
    disjoint_ranges dest (lengthZ old + lengthZ source + 1)
                    src (lengthZ source + 1).


Definition wcsncat_callable
    (memory : wide_memory) (dest src count : Z) : Prop :=
  exists old source read_extent,
    string_at memory dest old /\
    bounded_source_at memory src count source read_extent /\
    readable_range memory dest (lengthZ old + lengthZ source + 1).


Definition wmemcpy_callable
    (memory : wide_memory) (dest src count : Z) : Prop :=
  readable_range memory dest count /\
  readable_range memory src count /\
  disjoint_ranges dest count src count.

Definition wmemmove_callable
    (memory : wide_memory) (dest src count : Z) : Prop :=
  readable_range memory dest count /\ readable_range memory src count.

Definition wmemset_callable
    (memory : wide_memory) (dest _value count : Z) : Prop :=
  readable_range memory dest count.

Definition wcscoll_callable
    (_locale : locale_model) (memory : wide_memory)
    (lhs rhs : pointer) : Prop :=
  exists left right,
    string_at memory lhs left /\ string_at memory rhs right.

Definition wcsxfrm_callable
    (_locale : locale_model) (memory : wide_memory)
    (dest : option pointer) (src count : Z) : Prop :=
  exists source,
    string_at memory src source /\
    0 <= count /\
    match dest with
    | None => count = 0
    | Some p =>
        if Z.eq_dec count 0
        then valid_pointer memory p
        else readable_range memory p count /\
             disjoint_ranges p count src (lengthZ source + 1)
    end.

(** Exact transition relations for the seven destination-pointer operations. *)
Definition wcscpy_step
    (before : wide_memory) (dest src actual_return : Z)
    (after : wide_memory) : Prop :=
  wcscpy before dest src = Some (actual_return, after).

Definition wcsncpy_step
    (before : wide_memory) (dest src count actual_return : Z)
    (after : wide_memory) : Prop :=
  wcsncpy before dest src count = Some (actual_return, after).

Definition wcscat_step
    (before : wide_memory) (dest src actual_return : Z)
    (after : wide_memory) : Prop :=
  wcscat before dest src = Some (actual_return, after).

Definition wcsncat_step
    (before : wide_memory) (dest src count actual_return : Z)
    (after : wide_memory) : Prop :=
  wcsncat before dest src count = Some (actual_return, after).

Definition wmemcpy_step
    (before : wide_memory) (dest src count actual_return : Z)
    (after : wide_memory) : Prop :=
  wmemcpy before dest src count = Some (actual_return, after).

Definition wmemmove_step
    (before : wide_memory) (dest src count actual_return : Z)
    (after : wide_memory) : Prop :=
  wmemmove before dest src count = Some (actual_return, after).

Definition wmemset_step
    (before : wide_memory) (dest value count actual_return : Z)
    (after : wide_memory) : Prop :=
  wmemset before dest value count = Some (actual_return, after).

Definition same_sign (actual canonical : Z) : Prop :=
  Z.compare actual 0 = Z.compare canonical 0.

(** Flat-memory relation used by the public [wcscoll] specification. *)
Definition wcscoll_flat_step
    (locale : locale_model) (before : wide_memory)
    (lhs rhs result : Z) (after : wide_memory) : Prop :=
  exists left right,
    string_at before lhs left /\
    string_at before rhs right /\
    after = before /\
    same_sign result
      (compare_payloads
        (locale_transform locale left)
        (locale_transform locale right)).

(** Flat-memory relation used by the public [wcsxfrm] specification. *)
Definition wcsxfrm_flat_step
    (locale : locale_model) (before : wide_memory)
    (dest : option pointer) (src count result : Z)
    (after : wide_memory) : Prop :=
  wcsxfrm_step (locale_transform locale)
    before dest src count result after.

(** Two-array observer relation used by the locale strength obligation. *)
Definition wcscoll_public_step
    (locale : locale_model) (lhs rhs : wide_memory) (result : Z)
    (lhs_after rhs_after : wide_memory) : Prop :=
  exists left right,
    string_at lhs 0 left /\
    string_at rhs 0 right /\
    lhs_after = lhs /\ rhs_after = rhs /\
    same_sign result
      (compare_payloads
        (locale_transform locale left)
        (locale_transform locale right)).

Definition locale_write_prefix
    (before values : wide_memory) : wide_memory :=
  values ++ skipn (List.length values) before.

Definition xfrm_destination_domain
    (count : Z) (dest : option wide_memory) : Prop :=
  0 <= count /\
  match dest with
  | None => count = 0
  | Some storage => count <= lengthZ storage
  end.

(** Two-array transformer relation used by the locale strength obligation. *)
Definition wcsxfrm_public_step
    (locale : locale_model) (source : wide_memory)
    (dest : option wide_memory) (count result : Z)
    (source_after : wide_memory) (dest_after : option wide_memory) : Prop :=
  exists payload,
    string_at source 0 payload /\
    xfrm_destination_domain count dest /\
    source_after = source /\
    result = lengthZ (locale_transform locale payload) /\
    if Z.eq_dec count 0
    then dest_after = dest
    else
      if Z_lt_dec (lengthZ (locale_transform locale payload)) count
      then exists storage,
        dest = Some storage /\
        dest_after = Some
          (locale_write_prefix storage
            (locale_transform locale payload ++ [0]))
      else exists before after,
        dest = Some before /\ dest_after = Some after /\
        List.length after = List.length before.


