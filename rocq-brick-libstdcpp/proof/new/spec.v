Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.new.pred.
Require Import skylabs.brick.libstdcpp.new.inc_new_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.
  Context `{alignment_support : !allocation_alignment_support σ}.

  cpp.spec "operator new(std::size_t, const std::nothrow_t&)" as operator_new_nothrow with
    (\arg{sz}        "sz"      (Vn sz)
     \arg{nothrow_p} "nothrow" (Vref nothrow_p)
     \post{p}[Vptr p]
        if bool_decide (p = nullptr) then emp
        else p |-> (blockR sz 1$m **
                    alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                    allocatedR 1 false None sz)).

  cpp.spec "operator new(std::size_t, enum std::align_val_t, const std::nothrow_t&)" as operator_new_align_nothrow with
    (\arg{sz} "sz" (Vn sz)
     \arg{al} "al" (Vn al)
     \arg{nothrow_p} "nothrow" (Vref nothrow_p)
     \require supported_alignment al
     \post{p}[Vptr p]
        if bool_decide (p = nullptr) then emp
        else p |-> (blockR sz 1$m ** alignedR al **
                    allocatedR 1 false (Some al) sz)).

  (* Consult <<spec_exc.v>> for a specification of <<operator new(size_t)>>, the
     "default" <<new>>.
   *)

  cpp.spec "operator delete(void*)" as operator_delete with
      (\arg{p} "p" (Vptr p)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 false None sz ** blockR sz 1$m)
       \post emp).

  cpp.spec "operator delete(void*, enum std::align_val_t)" as operator_delete_align with
      (\arg{p} "p" (Vptr p)
       \arg{al} "al" (Vn al)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 false (Some al) sz **
                               blockR sz 1$m ** alignedR al)
       \post emp).

(*  #[ignore_missing] *)
  cpp.spec "operator delete(void*, std::size_t, enum std::align_val_t)" as operator_delete_size_align with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \pre if bool_decide (p = nullptr) then emp
            else p |-> (allocatedR 1 false (Some al) sz ** blockR sz 1$m ** alignedR al)
       \post emp).

(*  #[ignore_missing] *)
  cpp.spec "operator delete(void*, std::size_t)" as operator_delete_size with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \pre if bool_decide (p = nullptr) then emp
            else p |-> (allocatedR 1 false None sz ** blockR sz 1$m)
       \post emp).

  (** ** Array <<new>> and <<delete>> *)
  cpp.spec "operator new[](std::size_t, const std::nothrow_t&)" as operator_new_array_nothrow with
      (\arg{sz} "sz" (Vn sz)
       \arg{nothrow_p} "" (Vptr nothrow_p)
       \post{p}[Vptr p]
          if bool_decide (p = nullptr) then emp
          else p |-> (blockR sz 1$m **
                      alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                      allocatedR 1 true None sz)).

  cpp.spec "operator new[](std::size_t, enum std::align_val_t, const std::nothrow_t&)" as operator_new_array_align_nothrow with
      (\arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \arg{nothrow_p} "nothrow" (Vref nothrow_p)
       \require supported_alignment al
       \post{p}[Vptr p]
          if bool_decide (p = nullptr) then emp
          else p |-> (blockR sz 1$m ** alignedR al **
                      allocatedR 1 true (Some al) sz)).

  cpp.spec "operator delete[](void*)" as operator_delete_array with
      (\arg{p} "p" (Vptr p)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 true None sz ** blockR sz 1$m)
       \post emp).

  cpp.spec "operator delete[](void*, std::size_t)" as operator_delete_array_size with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \pre  if bool_decide (p = nullptr) then emp
             else p |-> (allocatedR 1 true None sz ** blockR sz 1$m)
       \post emp).

  cpp.spec "operator delete[](void*, enum std::align_val_t)" as operator_delete_array_align with
      (\arg{p} "p" (Vptr p)
       \arg{al} "al" (Vn al)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 true (Some al) sz **
                               blockR sz 1$m ** alignedR al)
       \post emp).

  cpp.spec "operator delete[](void*, std::size_t, enum std::align_val_t)" as operator_delete_array_size_align with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \pre if bool_decide (p = nullptr) then emp
            else p |-> (allocatedR 1 true (Some al) sz **
                         blockR sz 1$m ** alignedR al)
       \post emp).

End with_cpp.

NES.Begin alloc.

  (* TODO: fix this *)
  Abbreviation interface := (operator_new_nothrow ** operator_delete ** valid_ptr (_global "nothrow")).
NES.End alloc.

#[global] Hint Extern 1000 (SpecFor "operator new(unsigned long)"%cpp_name _) =>
   (idtac "<<operator new(size_t)>>'s specification requires exceptions."
          "See [skylabs.brick.libstdcpp.new.spec_exc] for more information about it.";
    exact (SpecFor.mk _ emp)) : typeclass_instances.

#[global] Hint Extern 1000 (SpecFor "operator new[](unsigned long)"%cpp_name _) =>
  (idtac "<<operator new[](size_t)>>'s specification requires exceptions."
     "See [skylabs.brick.libstdcpp.new.spec_exc] for more information about it.";
   exact (SpecFor.mk _ emp)) : typeclass_instances.
