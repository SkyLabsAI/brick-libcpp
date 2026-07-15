
From Stdlib Require Import List ZArith Lia.
Import ListNotations.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.

(** Mathematical value stored in one [wchar_t] object. *)
Definition wchar := Z.
(** Pointer-relative index measured in [wchar_t] objects. *)
Definition offset := Z.
(** Client-visible model of readable wide-character storage. *)
Definition wide_array := list wchar.

Fixpoint first_nul_from (xs : wide_array) (i : Z) : option offset :=
  match xs with
  | [] => None
  | x :: tail =>
      if Z.eqb x 0 then Some i else first_nul_from tail (i + 1)
  end.

Definition first_nul (xs : wide_array) : option offset :=
  first_nul_from xs 0.

Definition has_nul (xs : wide_array) : bool :=
  match first_nul xs with
  | Some _ => true
  | None => false
  end.

Definition compare_wchar (x y : wchar) : Z :=
  if Z.ltb x y then -1 else if Z.ltb y x then 1 else 0.

Fixpoint wcscmp_core (lhs rhs : wide_array) : Z :=
  match lhs, rhs with
  | x :: xs, y :: ys =>
      let order := compare_wchar x y in
      if Z.eqb order 0
      then if Z.eqb x 0 then 0 else wcscmp_core xs ys
      else order
  | _, _ => 0
  end.

Fixpoint compare_at_most
    (fuel : nat) (lhs rhs : wide_array) : option Z :=
  match fuel with
  | O => Some 0
  | S fuel' =>
      match lhs, rhs with
      | x :: xs, y :: ys =>
          let order := compare_wchar x y in
          if Z.eqb order 0
          then
            if Z.eqb x 0
            then Some 0
            else compare_at_most fuel' xs ys
          else Some order
      | _, _ => None
      end
  end.

Fixpoint compare_counted
    (fuel : nat) (lhs rhs : wide_array) : option Z :=
  match fuel with
  | O => Some 0
  | S fuel' =>
      match lhs, rhs with
      | x :: xs, y :: ys =>
          let order := compare_wchar x y in
          if Z.eqb order 0
          then compare_counted fuel' xs ys
          else Some order
      | _, _ => None
      end
  end.

Fixpoint nul_within (fuel : nat) (xs : wide_array) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match xs with
      | [] => false
      | x :: tail =>
          if Z.eqb x 0 then true else nul_within fuel' tail
      end
  end.

Definition counted_array (count : Z) (xs : wide_array) : bool :=
  Z.leb 0 count && Nat.leb (Z.to_nat count) (List.length xs).

Definition wcsncmp_readable (count : Z) (xs : wide_array) : bool :=
  Z.leb 0 count &&
  (Nat.leb (Z.to_nat count) (List.length xs) ||
   nul_within (Z.to_nat count) xs).

Fixpoint first_in
    (fuel : nat) (xs : wide_array) (target : wchar) (i : Z)
    : option offset :=
  match fuel, xs with
  | O, _ => None
  | S _, [] => None
  | S fuel', x :: tail =>
      if Z.eqb x target
      then Some i
      else first_in fuel' tail target (i + 1)
  end.

Fixpoint first_through_nul
    (xs : wide_array) (target : wchar) (i : Z) : option offset :=
  match xs with
  | [] => None
  | x :: tail =>
      if Z.eqb x target
      then Some i
      else if Z.eqb x 0
           then None
           else first_through_nul tail target (i + 1)
  end.

Fixpoint last_through_nul
    (xs : wide_array) (target : wchar) (i : Z)
    (last : option offset) : option offset :=
  match xs with
  | [] => last
  | x :: tail =>
      let last' := if Z.eqb x target then Some i else last in
      if Z.eqb x 0
      then last'
      else last_through_nul tail target (i + 1) last'
  end.

(** Partial standard-domain calls used to state public callability. *)
Definition wcslen_call (xs : wide_array) : option Z := first_nul xs.

Definition wcscmp_call (lhs rhs : wide_array) : option Z :=
  if has_nul lhs && has_nul rhs
  then Some (wcscmp_core lhs rhs)
  else None.

Definition wcsncmp_call
    (lhs rhs : wide_array) (count : Z) : option Z :=
  if wcsncmp_readable count lhs && wcsncmp_readable count rhs
  then compare_at_most (Z.to_nat count) lhs rhs
  else None.

Definition wcschr_call
    (xs : wide_array) (target : wchar) : option (option offset) :=
  if has_nul xs
  then Some (first_through_nul xs target 0)
  else None.

Definition wcsrchr_call
    (xs : wide_array) (target : wchar) : option (option offset) :=
  if has_nul xs
  then Some (last_through_nul xs target 0 None)
  else None.

Definition wmemcmp_call
    (lhs rhs : wide_array) (count : Z) : option Z :=
  if counted_array count lhs && counted_array count rhs
  then compare_counted (Z.to_nat count) lhs rhs
  else None.

Definition wmemchr_call
    (xs : wide_array) (target : wchar) (count : Z)
    : option (option offset) :=
  if counted_array count xs
  then Some (first_in (Z.to_nat count) xs target 0)
  else None.

(** Total public result models.  Specs expose them only under the corresponding
    callable predicate, so the fallback branch is never observable. *)
Definition wcslen (xs : wide_array) : Z :=
  match wcslen_call xs with Some result => result | None => 0 end.

Definition wcscmp (lhs rhs : wide_array) : Z :=
  match wcscmp_call lhs rhs with Some result => result | None => 0 end.

Definition wcsncmp (lhs rhs : wide_array) (count : Z) : Z :=
  match wcsncmp_call lhs rhs count with
  | Some result => result
  | None => 0
  end.

Definition wcschr (xs : wide_array) (target : wchar) : option offset :=
  match wcschr_call xs target with Some result => result | None => None end.

Definition wcsrchr (xs : wide_array) (target : wchar) : option offset :=
  match wcsrchr_call xs target with Some result => result | None => None end.

Definition wmemcmp (lhs rhs : wide_array) (count : Z) : Z :=
  match wmemcmp_call lhs rhs count with
  | Some result => result
  | None => 0
  end.

Definition wmemchr
    (xs : wide_array) (target : wchar) (count : Z) : option offset :=
  match wmemchr_call xs target count with
  | Some result => result
  | None => None
  end.

(** Exact public preconditions; they expose only defined-domain evidence. *)

Definition wcslen_callable (xs : wide_array) : Prop :=
  has_nul xs = true.

Definition wcscmp_callable (lhs rhs : wide_array) : Prop :=
  has_nul lhs = true /\ has_nul rhs = true.

Definition wcsncmp_callable
    (lhs rhs : wide_array) (count : Z) : Prop :=
  wcsncmp_readable count lhs = true /\
  wcsncmp_readable count rhs = true.

Definition wcschr_callable (xs : wide_array) (_target : wchar) : Prop :=
  has_nul xs = true.

Definition wcsrchr_callable (xs : wide_array) (_target : wchar) : Prop :=
  has_nul xs = true.

Definition wmemcmp_callable
    (lhs rhs : wide_array) (count : Z) : Prop :=
  counted_array count lhs = true /\ counted_array count rhs = true.

Definition wmemchr_callable
    (xs : wide_array) (_target count : Z) : Prop :=
  counted_array count xs = true.




(** Observer transitions used by the read-only footprint obligations. *)
Definition wcslen_step
    (before : wide_array) (result : Z) (after : wide_array) : Prop :=
  wcslen_callable before /\ result = wcslen before /\ after = before.

Definition wcscmp_step
    (lhs rhs : wide_array) (result : Z)
    (lhs' rhs' : wide_array) : Prop :=
  wcscmp_callable lhs rhs /\ result = wcscmp lhs rhs /\
  lhs' = lhs /\ rhs' = rhs.

Definition wcsncmp_step
    (lhs rhs : wide_array) (count result : Z)
    (lhs' rhs' : wide_array) : Prop :=
  wcsncmp_callable lhs rhs count /\ result = wcsncmp lhs rhs count /\
  lhs' = lhs /\ rhs' = rhs.

Definition wcschr_step
    (before : wide_array) (target : wchar) (result : option offset)
    (after : wide_array) : Prop :=
  wcschr_callable before target /\ result = wcschr before target /\
  after = before.

Definition wcsrchr_step
    (before : wide_array) (target : wchar) (result : option offset)
    (after : wide_array) : Prop :=
  wcsrchr_callable before target /\ result = wcsrchr before target /\
  after = before.

Definition wmemcmp_step
    (lhs rhs : wide_array) (count result : Z)
    (lhs' rhs' : wide_array) : Prop :=
  wmemcmp_callable lhs rhs count /\ result = wmemcmp lhs rhs count /\
  lhs' = lhs /\ rhs' = rhs.

Definition wmemchr_step
    (before : wide_array) (target count : Z) (result : option offset)
    (after : wide_array) : Prop :=
  wmemchr_callable before target count /\
  result = wmemchr before target count /\ after = before.
(* Seeded for live rocq-ed authoring. *)
