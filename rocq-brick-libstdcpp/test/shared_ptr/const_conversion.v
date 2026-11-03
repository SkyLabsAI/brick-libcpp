(** Check the template flags and complete handle layout against libstdc++.
    These tests use no shared_ptr method spec and do not open its invariant. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.

Set Default Goal Selector "!".
Import linearity.

#[elaborate]
cpp.prog source prog cpp:{{
#include <memory>
static_assert(sizeof(std::shared_ptr<int>) == 16);
static_assert(sizeof(std::shared_ptr<const int>) == 16);
static_assert(sizeof(std::shared_ptr<int[]>) == 16);
static_assert(sizeof(std::shared_ptr<const int[4]>) == 16);
static_assert(sizeof(std::shared_ptr<void>) == 16);
static_assert(sizeof(std::shared_ptr<const void>) == 16);
}}.

Definition handle_types : list type :=
  [Tint; Tconst Tint; Tincomplete_array Tint; Tconst (Tarray Tint 4);
   Tvoid; Tconst Tvoid].

Example handle_layouts_match :
  forallb (fun ty => bool_decide
    (type_table_le (types (shared_ptr_const_tu ty)) (types source)))
    handle_types = true.
Proof. vm_compute. reflexivity. Qed.

Section with_cpp.
  Context `{Sigma : cpp_logic} {CU : genv}.

  Example shared_const_roundtrip id i Rpiece owned (handle : ptr) :
    handle |-> SharedPtrR (Tconst Tint) 1$m id i Rpiece owned
    |-- wp_make_const source handle (Tnamed (SP_name (Tconst Tint)))
      (wp_make_mutable source handle (Tnamed (SP_name (Tconst Tint)))
        (handle |-> SharedPtrR (Tconst Tint) 1$m id i Rpiece owned)).
  Proof. go. Qed.

  Example null_array_const_roundtrip (handle : ptr) :
    handle |-> NullSharedPtrR (Tincomplete_array Tint) 1$m
    |-- wp_make_const source handle
      (Tnamed (SP_name (Tincomplete_array Tint)))
      (wp_make_mutable source handle
        (Tnamed (SP_name (Tincomplete_array Tint)))
        (handle |-> NullSharedPtrR (Tincomplete_array Tint) 1$m)).
  Proof. go. Qed.
End with_cpp.
