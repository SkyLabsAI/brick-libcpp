Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.string.pred.
Require skylabs.brick.libstdcpp.test.vector.cpp_class.test_cpp.
#[local] Abbreviation source := test_cpp.source.

NES.Begin Plain.
  (* Exercise field lookup independently of fractional splitting for vector.R_alloc. *)
  cpp.class "Plain" prefix "" from source dataclass[no_cfrac] { default_specs }.
NES.End Plain.

Check (Plain.v : Plain.T -> list Z).
