Require Export skylabs.brick.libstdcpp.thread.inc_hpp.

Require Export skylabs.brick.libstdcpp.mutex.requirements.
Require Export skylabs.auto.cpp.prelude.spec.
Require Export skylabs.auto.cpp.prelude.proof.

Require Export skylabs.cpp.spec.concepts.

#[global] Instance should_inline_std_ref ty1 ty2 :
  ShouldInlineFunction {%cpp_name "std::ref<$ty1>($ty2 &)"} := {}.
#[global] Instance should_inline_std_cref ty1 ty2 :
  ShouldInlineFunction {%cpp_name "std::cref<$ty1>($ty2 &)"} := {}.
#[global] Instance should_inline_std_forward ty1 ty2 :
  ShouldInlineFunction {%cpp_name "std::forward<$ty1>($ty2)"} := {}.
#[global] Instance should_inline_std_move ty1 ty2 :
  ShouldInlineFunction {%cpp_name "std::move<$ty1>($ty2)"} := {}.


(* for [std::ref] and [std::cref] *)
NES.Begin std.reference_wrapper.

mlock
Definition R `{Σ : cpp_logic, σ : genv} (ty : type) (q : cQp.t) (x : ptr) :=
  _field  {%cpp_name "std::reference_wrapper<$ty>::_M_data"} |-> ptrR<ty> q x **
  structR {%cpp_name "std::reference_wrapper<$ty>"} q.
#[only(hint_opaque,type_ptr,cfractional,ascfractional)] derive R.
Definition learn_spec `{Σ : cpp_logic, σ : genv} := Learn (req_eq ==> any ==> learn_eq ==> learn_hints.fin) R.
#[only(learn)] derive learn_spec.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context (ty : type).

  (* challenging for cpp.spec name lookup *)
  Definition reference_wrapper_ctor _a _b _c _d :=
    specify.template.ctor {%cpp_name "std::reference_wrapper<$ty>"} [Atype _a; Atype _b; Atype _c] [_d] $
      \this this
      \arg{x} "x" (Vptr x)
      \post this |-> reference_wrapper.R ty 1$m x.
  #[global] Hint Opaque reference_wrapper_ctor : sl_opacity.
  Definition SpecFor_reference_wrapper_ctor := RegisterSpec reference_wrapper_ctor.
  #[global] Existing Instance SpecFor_reference_wrapper_ctor.

  cpp.spec "std::reference_wrapper<$ty>::~reference_wrapper()" as reference_wrapper_dtor
         from source
       ( \\with
         \this this
         \pre{x} this |-> R ty 1$m x
         \post emp ).

  cpp.spec "std::reference_wrapper<$ty>::reference_wrapper(const std::reference_wrapper<$ty>&)"
         as reference_wrapper_copy_ctor
         from source
       ( \\with
         \this this
         \arg{otherp} "other" (Vref otherp)
         \prepost{q x} otherp |-> reference_wrapper.R ty q x
         \post*        this |-> reference_wrapper.R ty 1$m x
         \post emp ).

  cpp.spec "std::reference_wrapper<$ty>::operator $ty &() const"
         as reference_wrapper_cast_op
         from source
       ( \\with
         \this this
         \prepost{q x} this |-> reference_wrapper.R ty q x
         \post[Vptr x] emp ).

End with_cpp.
NES.End std.reference_wrapper.
