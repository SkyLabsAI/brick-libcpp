Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.string.pred.
Require skylabs.brick.libstdcpp.test.vector.cpp_class.test_cpp.
#[local] Abbreviation source := test_cpp.source.

NES.Begin VectorImplData.
  cpp.class "std::_Vector_base<unsigned long, std::allocator<unsigned long>>::_Vector_impl_data"
    prefix "" from source dataclass.
NES.End VectorImplData.

NES.Begin VectorImpl.
  cpp.class "std::_Vector_base<unsigned long, std::allocator<unsigned long>>::_Vector_impl"
    prefix "" from source dataclass .
NES.End VectorImpl.

NES.Begin VectorBase.
  cpp.class "std::_Vector_base<unsigned long, std::allocator<unsigned long>>"
    prefix "" from source dataclass.
NES.End VectorBase.

NES.Begin Vec.
  cpp.class "std::vector<unsigned long, std::allocator<unsigned long>>"
    prefix "" from source dataclass.
NES.End Vec.
