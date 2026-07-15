
Require Import skylabs.auto.cpp.specs.
Require Export skylabs.brick.libstdcpp.cwchar_copy.model.

#[local] Set Primitive Projections.

(** A single authoritative view of all [wchar_t] objects that may be read or
    written by a call.  Owning the complete logical memory makes overlap and
    unchanged-suffix guarantees observable in the postcondition. *)
Section with_cpp.
  Context `{Sigma : cpp_logic} {sigma : genv}.

  Parameter wide_memoryR : cQp.t -> wide_memory -> Rep.

  (** The current collation transform.  This resource is returned unchanged;
      it connects [wcscoll] and [wcsxfrm] to one locale model. *)
  Parameter current_collationR : locale_model -> mpred.
End with_cpp.

