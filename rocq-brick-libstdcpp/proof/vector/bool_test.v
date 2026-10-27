(** Exercise packed-bit fill construction, proxy update/read, move, and both
    moved-from and live destruction. This checks the assumed library API. *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.vector.bool_spec.

Set Default Goal Selector "!".
Set Warnings "+sl-transparent-constants".
Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

#[elaborate]
cpp.prog source prog cpp:{{
#include <vector>
bool bit_roundtrip(bool value, std::allocator<bool> const& allocator) {
    std::vector<bool> bits(2, false, allocator);
    bits[1] = value;
    std::vector<bool> moved(static_cast<std::vector<bool>&&>(bits));
    return moved[1];
}
}}.

Section with_cpp.
  Context `{Sigma : cpp_logic, MOD : source ⊧ σ}.

  cpp.spec "bit_roundtrip(bool, const std::allocator<bool>&)" from source as bit_roundtrip_spec with (
    \arg{value : bool} "value" (Vbool value)
    \arg{allocp : ptr} "allocator" (Vref allocp)
    \prepost{qalloc} allocp |-> std.allocator.R Tbool qalloc ()
    \post[Vbool value] emp
  ).

  Lemma bit_roundtrip_ok : verify[source] bit_roundtrip_spec.
  Proof using MOD.
    verify_spec.
    go.
    iExists qalloc.
    go.
    iExists bits_addr, [false; false].
    go.
    iExists moved_addr, (cQp.mut 1), [false; value].
    go.
  Qed.
End with_cpp.
