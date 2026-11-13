Require Import skylabs.auto.cpp.prelude.spec.

Require Import skylabs.brick.libstdcpp.utility.inc_utility_cpp.


#[local] Set Warnings "+sl-transparent-constants".

(* Inline any move/forward specialization. *)
#[global] Instance inline_move_spec tmpl_arg arg_type :
  ShouldInlineFunction
    (Ninst
      ("std" .:: (Nfunction function_qualifiers.N "move" [tmpl_arg]))
      [Atype arg_type]) := {}.

#[global] Instance inline_forward_spec tmpl_arg arg_type :
  ShouldInlineFunction
    (Ninst
      ("std" .:: (Nfunction function_qualifiers.N "forward" [tmpl_arg]))
      [Atype arg_type]) := {}.
