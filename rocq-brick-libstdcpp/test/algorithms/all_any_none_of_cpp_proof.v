(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.algorithms.hints.
Require Import skylabs.brick.libstdcpp.test.algorithms.all_any_none_of_cpp.

Require Import skylabs.auto.cpp.prelude.test.

(** * Predicates

    Each predicate class gets the generated representation [R] and specifications of
    its special members, a [BundledRep] for its model [T], and a [Predicate] instance
    describing it to the algorithms. *)

Module Positive.
  Import concepts.
  cpp.class "Positive" prefix "" from source dataclass { copyable ; movable ; destructible }.
  (* [R] ignores the model, whose type has a single value: pin it, so that a
     specification binding it does not leave it unbound. *)
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "Positive" T :=
    {| objR q m := (R q m ** [| m = Build_T |])%I |}.
End Positive.

Module PositiveRef.
  Import concepts.
  cpp.class "PositiveRef" prefix "" from source dataclass { copyable ; movable ; destructible }.
  (* [R] ignores the model, whose type has a single value: pin it, so that a
     specification binding it does not leave it unbound. *)
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "PositiveRef" T :=
    {| objR q m := (R q m ** [| m = Build_T |])%I |}.
End PositiveRef.

Module IncPositive.
  Import concepts.
  cpp.class "IncPositive" prefix "" from source dataclass { copyable ; movable ; destructible }.
  (* [R] ignores the model, whose type has a single value: pin it, so that a
     specification binding it does not leave it unbound. *)
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "IncPositive" T :=
    {| objR q m := (R q m ** [| m = Build_T |])%I |}.
End IncPositive.

Module CountingPositive.
  Import concepts.
  cpp.class "CountingPositive" prefix "" from source dataclass { copyable ; movable ; destructible }.
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "CountingPositive" T := {| objR := R |}.
  #[global] Hint Opaque calls : sl_opacity.
End CountingPositive.

Module Logger.
  Import concepts.
  cpp.class "Logger" prefix "" from source dataclass { copyable ; movable ; destructible }.
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "Logger" T := {| objR := R |}.
  #[global] Hint Opaque log len : sl_opacity.

  (** The buffer holds the [xs] logged so far, followed by zeros. *)
  Abbreviation bufR xs :=
    (array_sliceR "int" 0 (lengthZ xs) (fun x => intR 1$m x) xs **
     array_sliceR "int" (lengthZ xs) 3 (fun x => intR 1$m x) (replicate (3 - length xs) 0%Z))
    (only parsing).
End Logger.

(** The closure type of the lambda in <<TestLambda>>, passed as a temporary. *)
Module Big.
  Import concepts.
  cpp.class "TestLambda()::@0" prefix "" from source dataclass { copyable ; movable ; destructible }.
  (* [R] ignores the model, whose type has a single value: pin it, so that a
     specification binding it does not leave it unbound. *)
  #[global] Instance rep `{Σ : cpp_logic, σ : genv} : BundledRep "TestLambda()::@0" T :=
    {| objR q m := (R q m ** [| m = Build_T |])%I |}.
End Big.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : all_any_none_of_cpp.source ⊧ σ}.

  #[local] Instance Positive_pred : std.Predicate "Positive" Positive.T Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 0)%Z).
  #[local] Instance PositiveRef_pred : std.Predicate "PositiveRef" PositiveRef.T Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 0)%Z).
  (** Defined except on <<INT_MAX>>. *)
  #[local] Instance IncPositive_pred : std.Predicate "IncPositive" IncPositive.T Z :=
    {| std.pred_test _ x := bool_decide (x > 0)%Z;
       std.pred_pre _ _ x := (x < 2147483647)%Z;
       std.pred_inv _ _ := emp |}.
  (** Counts modulo [2^32]. *)
  #[local] Instance Counting_pred : std.Predicate "CountingPositive" CountingPositive.T Z :=
    {| std.pred_test _ x := bool_decide (x > 0)%Z;
       std.pred_pre _ _ _ := True;
       std.pred_inv m hist := CountingPositive.calls m |-> uintR 1$m (trim 32 (lengthZ hist)) |}.
  #[local] Instance Logger_pred : std.Predicate "Logger" Logger.T Z :=
    {| std.pred_test _ x := bool_decide (x > 0)%Z;
       std.pred_pre _ hist _ := (length hist < 3)%nat;
       std.pred_inv m hist :=
         Logger.log m |-> Logger.bufR hist ** Logger.len m |-> uintR 1$m (lengthZ hist) |}.
  #[local] Instance is_zero_pred : std.Predicate "bool(*)(int)" ptr Z :=
    std.pure_predicate (fun _ x => bool_decide (x = 0)%Z).
  #[local] Instance Big_pred : std.Predicate "TestLambda()::@0" Big.T Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 5)%Z).

  (** ** The callables' specifications, as their implementers would state them. *)

  cpp.spec "Positive::operator()(int) const" as positive_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q m} this |-> Positive.R q m
     \post[Vbool (bool_decide (x > 0)%Z)] emp).

  cpp.spec "PositiveRef::operator()(const int&) const" as positive_ref_spec with
    (\this this
     \arg{xp} "x" (Vref xp)
     \prepost{q m} this |-> PositiveRef.R q m
     \prepost{qx x} xp |-> intR qx x
     \post[Vbool (bool_decide (x > 0)%Z)] emp).

  cpp.spec "IncPositive::operator()(int) const" as inc_positive_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \require (x < 2147483647)%Z
     \prepost{q m} this |-> IncPositive.R q m
     \post[Vbool (bool_decide (x > 0)%Z)] emp).

  cpp.spec "CountingPositive::operator()(int) const" as counting_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q cp} this |-> CountingPositive.R q (CountingPositive.Build_T cp)
     \pre{n} cp |-> uintR 1$m n
     \post[Vbool (bool_decide (x > 0)%Z)] cp |-> uintR 1$m (trim 32 (n + 1))).

  cpp.spec "Logger::operator()(int) const" as logger_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q logp lenp} this |-> Logger.R q (Logger.Build_T logp lenp)
     \pre{xs} logp |-> Logger.bufR xs
     \pre lenp |-> uintR 1$m (lengthZ xs)
     \require (length xs < 3)%nat
     \post[Vbool (bool_decide (x > 0)%Z)]
       logp |-> Logger.bufR (xs ++ [x]) ** lenp |-> uintR 1$m (lengthZ (xs ++ [x]))).

  cpp.spec "is_zero(int)" as is_zero_spec with
    (\arg{x} "x" (Vint x)
     \post[Vbool (bool_decide (x = 0)%Z)] emp).

  cpp.spec "TestLambda()::@0::operator()(int) const" as big_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q m} this |-> Big.R q m
     \post[Vbool (bool_decide (x > 5)%Z)] emp).

  Lemma positive_ok : verify[source] positive_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma positive_ref_ok : verify[source] positive_ref_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma inc_positive_ok : verify[source] inc_positive_spec.
  Proof using MOD. verify_spec. go. iPureIntro. lia. Qed.
  Lemma counting_ok : verify[source] counting_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma logger_ok : verify[source] logger_spec.
  Proof using MOD.
    verify_spec. go.
    (* Expose the slot that [x] goes into. *)
    have -> : (3 - length xs = S (2 - length xs))%nat by lia.
    go. iPureIntro. f_equal. rewrite length_app /=. lia.
  Qed.
  Lemma is_zero_ok : verify[source] is_zero_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma big_ok : verify[source] big_spec.
  Proof using MOD. verify_spec. go. Qed.

  (** ** Clients

      Each client assumes the specification of the callable it passes, as for virtual
      calls ([vptrI]); [go] proves that it entails the algorithm's contract. *)

  cpp.spec "TestAllOf()" as test_all_of with (\persist positive_spec \post emp).
  Lemma test_all_of_ok : verify[source] test_all_of.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestAnyOf()" as test_any_of with (\persist positive_spec \post emp).
  Lemma test_any_of_ok : verify[source] test_any_of.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestNoneOf()" as test_none_of with (\persist positive_spec \post emp).
  Lemma test_none_of_ok : verify[source] test_none_of.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestEmpty()" as test_empty with
    (\persist inc_positive_spec \persist positive_ref_spec \post emp).
  Lemma test_empty_ok : verify[source] test_empty.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestByReference()" as test_by_reference with (\persist positive_ref_spec \post emp).
  Lemma test_by_reference_ok : verify[source] test_by_reference.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestShortCircuit()" as test_short_circuit with (\persist inc_positive_spec \post emp).
  Lemma test_short_circuit_ok : verify[source] test_short_circuit.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestFunctionPointer()" as test_function_pointer with (\persist is_zero_spec \post emp).
  Lemma test_function_pointer_ok : verify[source] test_function_pointer.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "TestCounting()" as test_counting with (\persist counting_spec \post emp).
  Lemma test_counting_ok : verify[source] test_counting.
  Proof using MOD. verify_spec. go. Qed.

  (** [go] does not instantiate the history [xs] that [logger_spec] quantifies over,
      because the only atom determining it also mentions [lengthZ xs]. The entailment
      between [logger_spec] and the contract is thus left to the client. *)
  cpp.spec "TestLogger()" as test_logger with (\persist logger_spec \post emp).
  Lemma test_logger_ok : verify[source] test_logger.
  Proof using MOD.
    verify_spec. go.
    iSplit. { iPureIntro. rewrite /fs_entails. go. iExists _. go. }
    go.
  Qed.

  (** The closure has no fields, so copying it leaves its (unique) model to pick. *)
  cpp.spec "TestLambda()" as test_lambda with (\persist big_spec \post emp).
  Lemma test_lambda_ok : verify[source] test_lambda.
  Proof using MOD. verify_spec. go. Qed.

  (** ** Linking *)

  Lemma positive_dtor_ok : verify[source] Positive.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma positive_ref_dtor_ok : verify[source] PositiveRef.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma inc_positive_dtor_ok : verify[source] IncPositive.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma counting_dtor_ok : verify[source] CountingPositive.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma logger_dtor_ok : verify[source] Logger.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Lemma big_dtor_ok : verify[source] Big.dtor_spec.
  Proof using MOD. verify_spec. go. Qed.

  Definition test_all_of_B := [LINK] test_all_of_ok.
  Definition test_any_of_B := [LINK] test_any_of_ok.
  Definition test_none_of_B := [LINK] test_none_of_ok.
  Definition test_empty_B := [LINK] test_empty_ok.
  Definition test_by_reference_B := [LINK] test_by_reference_ok.
  Definition test_short_circuit_B := [LINK] test_short_circuit_ok.
  Definition test_function_pointer_B := [LINK] test_function_pointer_ok.
  Definition test_counting_B := [LINK] test_counting_ok.
  Definition test_logger_B := [LINK] test_logger_ok.
  Definition test_lambda_B := [LINK] test_lambda_ok.
  Definition positive_dtor_B := [LINK] positive_dtor_ok.
  Definition positive_ref_dtor_B := [LINK] positive_ref_dtor_ok.
  Definition inc_positive_dtor_B := [LINK] inc_positive_dtor_ok.
  Definition counting_dtor_B := [LINK] counting_dtor_ok.
  Definition logger_dtor_B := [LINK] logger_dtor_ok.
  Definition big_dtor_B := [LINK] big_dtor_ok.
  (* <<&is_zero>> makes [is_zero_spec] a direct dependency of <<TestFunctionPointer>>. *)
  Definition is_zero_B := [LINK] is_zero_ok.
  #[local] Hint Resolve is_zero_B test_all_of_B test_any_of_B test_none_of_B test_empty_B
    test_by_reference_B test_short_circuit_B test_function_pointer_B test_counting_B
    test_logger_B test_lambda_B positive_dtor_B positive_ref_dtor_B inc_positive_dtor_B
    counting_dtor_B logger_dtor_B big_dtor_B : br_hints.

  (** The callables' specifications are assumed, as for virtual calls ([vptrI]). *)
  cpp.spec "main()" as main_spec with
    (\persist positive_spec \persist positive_ref_spec \persist inc_positive_spec
     \persist counting_spec \persist logger_spec \persist is_zero_spec \persist big_spec
     \post[Vint 0] emp).
  Lemma main_ok : verify[source] main_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition main_B := [LINK] main_ok.
  #[local] Hint Resolve main_B : br_hints.

  (** All the proofs above, linked against the algorithms' specifications. *)
  Lemma specs_ok :
    denoteModule source **
    ▷ ( std.all_of_spec (Tptr "int") "Positive" source **
        std.any_of_spec (Tptr "int") "Positive" source **
        std.none_of_spec (Tptr "int") "Positive" source **
        std.all_of_spec (Tptr "int") "PositiveRef" source **
        std.any_of_spec (Tptr "int") "PositiveRef" source **
        std.all_of_spec (Tptr "int") "IncPositive" source **
        std.any_of_spec (Tptr "int") "IncPositive" source **
        std.none_of_spec (Tptr "int") "IncPositive" source **
        std.all_of_spec (Tptr "int") "bool(*)(int)" source **
        std.all_of_spec (Tptr "int") "CountingPositive" source **
        std.all_of_spec (Tptr "int") "Logger" source **
        std.none_of_spec (Tptr "int") "TestLambda()::@0" source **
        std.cassert.specs )
    |-- main_spec.
  Proof using MOD.
    rewrite /std.cassert.specs. iIntros "[#? #(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)]".
    work.
  Qed.

  (** ** Undefined behavior

      Each of these functions has undefined behavior, so no specification of them can
      be proven. The proofs get stuck on the precondition that rules it out, which the
      [match]es check. *)

  (** The second element is tested, and overflows. *)
  cpp.spec "Overflow()" as overflow with
    (\persist inc_positive_spec \post{r}[Vbool r] emp).
  Lemma overflow_stuck : verify[source] overflow.
  Proof using MOD.
    verify_spec. go.
    match goal with |- context [ (2147483647 < 2147483647)%Z ] => idtac end.
  Abort.

  (** There is no function at [nullptr], and the range is not empty. *)
  cpp.spec "NullFunctionPointer()" as null_function_pointer with
    (\persist is_zero_spec \post{r}[Vbool r] emp).
  Lemma null_function_pointer_stuck : verify[source] null_function_pointer.
  Proof using MOD.
    verify_spec. go.
    match goal with |- context [ nullptr |-> cptrR _ ] => idtac end.
  Abort.

  (** [a + 2, a) is not a range: [2 <= 0] does not hold. *)
  cpp.spec "InvalidRange()" as invalid_range with
    (\persist positive_spec \post{r}[Vbool r] emp).
  Lemma invalid_range_stuck : verify[source] invalid_range.
  Proof using MOD.
    verify_spec. go.
    match goal with |- context [ std.array_spine _ _ _ 2 (rangeZ 2 0) 0 ] => idtac end.
  Abort.
End with_cpp.
