
Require Import skylabs.prelude.numbers.

#[local] Open Scope Z_scope.

Definition value_range := (Z * Z)%type.

Definition representable (range : value_range) (z : Z) : Prop :=
  fst range <= z <= snd range.

Definition signed32_range : value_range := (-2147483648, 2147483647).
Definition signed64_range : value_range :=
  (-9223372036854775808, 9223372036854775807).

Definition gcd (m n : Z) : Z := Z.gcd m n.

Definition lcm (m n : Z) : Z :=
  if m =? 0 then 0
  else if n =? 0 then 0
  else Z.abs ((m / gcd m n) * n).

Definition gcd_callable (range : value_range) (m n : Z) : Prop :=
  representable range (Z.abs m) /\
  representable range (Z.abs n).

Definition lcm_callable (range : value_range) (m n : Z) : Prop :=
  representable range (Z.abs m) /\
  representable range (Z.abs n) /\
  representable range (lcm m n).
(* Bootstrap file; substantive edits are made through the live rocq-ed session. *)
