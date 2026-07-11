
Require Import skylabs.brick.libstdcpp.memory.spec.addressof.
Require Import skylabs.brick.libstdcpp.test.existing_specs.memory_addressof_cpp.

Require Import skylabs.brick.libstdcpp.lib.tactics.
Require Import skylabs.brick.libstdcpp.cassert.spec.

Require Import skylabs.auto.cpp.prelude.test.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.

Module OverloadedAddress.
  Import concepts.
  cpp.class "overloaded_address" prefix "" from memory_addressof_cpp.source
    dataclass { destructible }.
End OverloadedAddress.

NES.Begin memory_addressof_clients.
  Section with_cpp.
    Context `{Sigma : cpp_logic, sigma : genv}.

    cpp.spec "test_public_addressof_int()" as test_public_addressof_int_spec from memory_addressof_cpp.source with (\post emp).
    cpp.spec "test_public_addressof_overloaded()" as test_public_addressof_overloaded_spec from memory_addressof_cpp.source with (\post emp).
    cpp.spec "test_internal_addressof_int()" as test_internal_addressof_int_spec from memory_addressof_cpp.source with (\post emp).
    cpp.spec "test_internal_addressof_overloaded()" as test_internal_addressof_overloaded_spec from memory_addressof_cpp.source with (\post emp).

    Lemma test_public_addressof_int_ok :
      denoteModule memory_addressof_cpp.source |--
        (▷ memory.addressof_spec "int" -∗
         ▷ std.cassert.assert_fail_spec -∗
         test_public_addressof_int_spec).
    Proof. verify_spec. go $usenamed=true. Qed.

    Lemma test_internal_addressof_int_ok :
      denoteModule memory_addressof_cpp.source |--
        (▷ memory.__addressof_spec "int" -∗
         ▷ std.cassert.assert_fail_spec -∗
         test_internal_addressof_int_spec).
    Proof. verify_spec. go $usenamed=true. Qed.

    Lemma test_public_addressof_overloaded_ok :
      denoteModule memory_addressof_cpp.source |--
        (▷ memory.addressof_spec "overloaded_address" -∗
         ▷ OverloadedAddress.dtor_spec -∗
         ▷ std.cassert.assert_fail_spec -∗
         test_public_addressof_overloaded_spec).
    Proof. verify_spec. go $usenamed=true. Qed.

    Lemma test_internal_addressof_overloaded_ok :
      denoteModule memory_addressof_cpp.source |--
        (▷ memory.__addressof_spec "overloaded_address" -∗
         ▷ OverloadedAddress.dtor_spec -∗
         ▷ std.cassert.assert_fail_spec -∗
         test_internal_addressof_overloaded_spec).
    Proof. verify_spec. go $usenamed=true. Qed.
  End with_cpp.
NES.End memory_addressof_clients.

