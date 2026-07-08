Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.mutex.inc_hpp.

Module defer_lock_t.
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Parameter R : forall {σ : genv}, cQp.t -> Rep.
  #[only(cfracsplittable, type_ptr="std::defer_lock_t")] derive R.

  Section with_RepFor.
    Import rep.RepFor.
    Import RepScheme.

    (* <<std::defer_lock_t>> is a marker type, but it is empty, so ownership is not really
       needed. *)
    #[global] Instance repfor `{Σ : cpp_logic} : rep.RepFor.C "std::defer_lock_t" [] emp := {}.
  End with_RepFor.

  cpp.spec "std::defer_lock_t::defer_lock_t(const std::defer_lock_t&)" as defer_lock_copy_ctor_spec from source with (
    \this this
    \arg{other} "other" (Vptr other)
    \prepost{q} other |-> R q
    \post this |-> R 1$m
  ).
  cpp.spec "std::defer_lock_t::~defer_lock_t()" as defer_lock_dtor_spec from source with (
    \this this
    \pre this |-> R 1$m
    \post emp
  ).
End with_cpp.
End defer_lock_t.
