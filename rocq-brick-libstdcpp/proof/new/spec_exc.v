Require Import skylabs.auto.cpp.specs.

Require Import skylabs.brick.libstdcpp.new.inc_new_cpp.
Require Export skylabs.brick.libstdcpp.new.spec.

Import cpp_notation.

(** This file specifies the throwing scalar and array allocation overloads,
    with and without an alignment parameter, provided by the C++ standard
    library. These functions communicate allocation
    failures using exceptions which BRiCk does not currently support.

    A common way to make this specification sound is to modify the
    implementations of these overloads to abort on allocation failure, e.g. by calling
    <<exit(1);>>. With this revision, the following [new_spec] is sound.

    If you require the use of exceptions in your development,
    please up-vote this feature request:
    <<https://github.com/skylabsai/BRiCk/issues/15>>.
 *)


#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{alignment_support : !allocation_alignment_support σ}.

  (** <<operator new(size_t)>> is not allowed to return <<nullptr>>, it
      signals failure by raising an exception.
   *)
  cpp.spec "operator new(std::size_t)" as new_spec with
      (\arg{sz} "sz"      (Vn sz)
       \post{p}[Vptr p] p |-> (blockR sz 1$m **
                               nonnullR **
                               alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                               allocatedR 1 false None sz)).

  cpp.spec "operator new(std::size_t, enum std::align_val_t)" as operator_new_align with
      (\arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \require supported_alignment al
       \post{p}[Vptr p]
           p |-> (blockR sz 1$m ** nonnullR ** alignedR al **
                  allocatedR 1 false (Some al) sz)).

  (** <<operator new[](size_t)>> is not allowed to return <<nullptr>>, it
      signals failure by raising an exception.
   *)
  cpp.spec "operator new[](std::size_t)" as operator_new_array with
      (\arg{sz} "sz" (Vn sz)
       \post{p}[Vptr p]
           p |-> (blockR sz 1$m **
                  nonnullR **
                  alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                  allocatedR 1 true None sz)).

  cpp.spec "operator new[](std::size_t, enum std::align_val_t)" as operator_new_array_align with
      (\arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \require supported_alignment al
       \post{p}[Vptr p]
           p |-> (blockR sz 1$m ** nonnullR ** alignedR al **
                  allocatedR 1 true (Some al) sz)).

End with_cpp.
