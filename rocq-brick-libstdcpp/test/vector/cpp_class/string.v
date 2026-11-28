Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.string.pred.
Require skylabs.brick.libstdcpp.test.vector.cpp_class.test_cpp.
#[local] Abbreviation source := test_cpp.source.

sl.lock Definition StrR `{Σ : cpp_logic} {σ : genv} (q : cQp.t) (s : BS.t) : Rep :=
  basic_stringR "char" q s.
#[only(lazy_unfold)] derive StrR.
cpp.class "std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>"
  prefix "Str" from source rep StrR.
NES.Begin WithString.
  cpp.class "WithString" prefix "" from source dataclass { default_specs }.
NES.End WithString.

Check WithString.default_ctor_spec.
Goal WithString.s WithString.default = BS.EmptyString.
Proof. reflexivity. Qed.
