Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.string.pred.
Require skylabs.brick.libstdcpp.test.vector.cpp_class.test_cpp.
#[local] Abbreviation source := test_cpp.source.

sl.lock Definition VecR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (xs : list Z) : Rep :=
  std.vector.R_alloc "unsigned long" "std::allocator<unsigned long>" q xs.
#[only(lazy_unfold,ascfractional,timeless,cfracvalid)] derive VecR.

Timeout 60 cpp.class "std::vector<unsigned long, std::allocator<unsigned long>>"
  prefix "Vec" from source rep VecR.
