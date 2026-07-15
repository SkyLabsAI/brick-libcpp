
Require Export skylabs.brick.libstdcpp.cwchar.model.
Require Import skylabs.auto.cpp.specs.
Require Import skylabs.cpp.array.
Require Import skylabs.cpp.slice.

#[local] Open Scope Z_scope.

(** Convert the physical, nonnegative [Vchar] encoding emitted by cpp2v into
    the public mathematical [list Z] model. *)
Definition decode_wide_array (raw : list N) : wide_array :=
  Z.of_N <$> raw.

(** Own all readable [wchar_t] objects in [raw], preserving the complete
    caller-provided array rather than only the prefix examined by an observer. *)
Section with_cpp.
  Context `{Sigma : cpp_logic} {sigma : genv}.

  Definition wide_arrayR (q : cQp.t) (raw : list N) : Rep :=
    array_sliceR Twchar 0 (lengthZ raw) (fun n : N => wcharR q n) raw.
End with_cpp.
#[global] Hint Opaque wide_arrayR : sl_opacity.

(* Seeded for live rocq-ed authoring. *)
