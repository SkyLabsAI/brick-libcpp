(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.test.algorithms.all_any_none_of_cpp.

Require Import skylabs.auto.cpp.prelude.test.

(** The closure type of the lambda in <<TestLambda>> has no C++ spelling, so
    [cpp.spec] cannot name its members. Its name is the first anonymous entity
    nested in the function, as in the generated AST. *)
Definition lambda_name : name :=
  Nscoped (Nglobal (Nfunction function_qualifiers.N "TestLambda" nil)) (Nanon 0).
Definition lambda_ty : type := Tnamed lambda_name.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Context `{MOD : all_any_none_of_cpp.source ⊧ σ}.

  (** Raw <<int*>> iterators into an array. *)
  #[local] Instance int_ptr_rep : BundledRep (Tptr "int") (ptr * Z) :=
    {| objR q st := ptrR<"int"> q (st.1 .[ "int" ! st.2 ]) |}.
  #[local] Instance int_ptr_ranges : std.HasRanges (Tptr "int") ptr Z :=
    std.array_ranges "int" (Tptr "int").

  Lemma int_array_restore basep n xs :
    std.array_spine "int" basep 1$m 0 (rangeZ 0 n) n **
    std.payload (Tptr "int") basep (fun x => intR 1$m x) (rangeZ 0 n) xs |--
    basep |-> array_sliceR "int" 0 n (fun v => intR 1$m v) xs.
  Proof. by rewrite (std.array_sliceR_eqv_spine_payload_rangeZ "int" (Tptr "int") 1$m). Qed.

  (** Discharges a call of an algorithm on the whole array [basep] of length [n]
      holding [xs], with element ownership [intR 1$m], using the adapter proof
      [Hcall] (with no extra premise); restores the array afterwards. *)
  Ltac call_on_array basep n xs model Hcall :=
    (* [go] instantiates the predicate model when it can read it off the object. *)
    first
      [ iExists basep, 0%Z, n, 1$m%cQp, model, (fun q x => intR q x), 1$m%cQp, xs,
          (std.Build_PredicateCall source MOD emp%I Hcall)
      | iExists basep, 0%Z, n, 1$m%cQp, (fun q x => intR q x), 1$m%cQp, xs,
          (std.Build_PredicateCall source MOD emp%I Hcall) ];
    go;
    iSplitR; [by iPureIntro; rewrite offset_ptr_sub_0|];
    iRename select (basep |-> array_sliceR _ _ _ _ _) into "Ha";
    iEval (rewrite (std.array_sliceR_eqv_spine_payload_rangeZ "int" (Tptr "int") 1$m)) in "Ha";
    iDestruct "Ha" as "[#Hs Hpay]";
    go;
    iFrame "Hs Hpay";
    iIntros (?) "(? & ? & ? & _ & Hpay & ? & ?)";
    iDestruct (int_array_restore with "[$Hs $Hpay]") as "?";
    iClear "Hs";
    go.

  (** The adapter proofs unfold [std.predicate_call], which is stated with
      [specify_raw]. *)
  #[local] Set Warnings "-sl-transparent-constants".

  (** A pure predicate with a member <<operator()>>. *)
  #[local] Instance Positive_rep : BundledRep "Positive" unit :=
    {| objR q _ := structR "Positive" q |}.
  #[local] Instance Positive_pred : std.Predicate "Positive" unit Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 0)%Z).

  cpp.spec "Positive::operator()(int) const" as positive_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q} this |-> structR "Positive" q
     \post[Vbool (bool_decide (x > 0)%Z)] emp).

  Lemma positive_ok : verify[source] positive_spec.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "Positive::~Positive()" as positive_dtor_spec with
    (\this this
     \pre this |-> structR "Positive" 1$m
     \post emp).

  Lemma positive_dtor_ok : verify[source] positive_dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition positive_dtor_B := [LINK] positive_dtor_ok.
  #[local] Hint Resolve positive_dtor_B : sl_opacity.

  Lemma positive_call_ok negated p xs :
    denoteModule source ⊢ □ emp -∗
      std.predicate_call negated (Tptr "int") "Positive" (fun q x => intR q x) p xs.
  Proof using MOD. destruct negated; std.verify_predicate_call positive_ok. Qed.

  cpp.spec "TestAllOf()" as test_all_of with (\post emp).
  Lemma test_all_of_ok : verify[source] test_all_of.
  Proof using MOD.
    verify_spec. go.
    call_on_array a_addr 2%Z [1; 2]%Z tt (positive_call_ok true tt [1; 2]%Z).
    call_on_array b_addr 2%Z [1; 0]%Z tt (positive_call_ok true tt [1; 0]%Z).
  Qed.

  cpp.spec "TestAnyOf()" as test_any_of with (\post emp).
  Lemma test_any_of_ok : verify[source] test_any_of.
  Proof using MOD.
    verify_spec. go.
    call_on_array a_addr 2%Z [0; 3]%Z tt (positive_call_ok false tt [0; 3]%Z).
    call_on_array b_addr 2%Z [0; -1]%Z tt (positive_call_ok false tt [0; -1]%Z).
  Qed.

  cpp.spec "TestNoneOf()" as test_none_of with (\post emp).
  Lemma test_none_of_ok : verify[source] test_none_of.
  Proof using MOD.
    verify_spec. go.
    call_on_array a_addr 2%Z [0; -1]%Z tt (positive_call_ok false tt [0; -1]%Z).
  Qed.

  (** A predicate that counts its calls through a pointer shared by all copies:
      its model is that pointer and [pred_inv] owns the counter. *)
  #[local] Instance Counting_rep : BundledRep "CountingPositive" ptr :=
    {| objR q cp :=
         structR "CountingPositive" q **
         _field "CountingPositive::calls" |-> ptrR<"int"> q cp |}.
  #[local] Instance Counting_pred : std.Predicate "CountingPositive" ptr Z :=
    {| std.pred_test _ x := bool_decide (x > 0)%Z;
       std.pred_inv cp k := cp |-> intR 1$m k |}.

  cpp.spec "CountingPositive::operator()(int) const" as counting_spec with
    (\this this
     \arg{x} "x" (Vint x)
     \prepost{q cp} this |-> (structR "CountingPositive" q **
                              _field "CountingPositive::calls" |-> ptrR<"int"> q cp)
     \pre{n} cp |-> intR 1$m n
     \require (0 <= n < 3)%Z
     \post[Vbool (bool_decide (x > 0)%Z)] cp |-> intR 1$m (n + 1)).

  Lemma counting_ok : verify[source] counting_spec.
  Proof using MOD. verify_spec. go. Qed.

  cpp.spec "CountingPositive::~CountingPositive()" as counting_dtor_spec with
    (\this this
     \pre{cp} this |-> (structR "CountingPositive" 1$m **
                        _field "CountingPositive::calls" |-> ptrR<"int"> 1$m cp)
     \post emp).

  Lemma counting_dtor_ok : verify[source] counting_dtor_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition counting_dtor_B := [LINK] counting_dtor_ok.
  #[local] Hint Resolve counting_dtor_B : sl_opacity.

  (** The counter cannot overflow: the algorithm makes at most [length xs] calls. *)
  Lemma counting_call_ok cp xs :
    lengthZ xs <= 3 ->
    denoteModule source ⊢ □ emp -∗
      std.predicate_call true (Tptr "int") "CountingPositive" (fun q x => intR q x) cp xs.
  Proof using MOD. intros Hlen. std.verify_predicate_call counting_ok. Qed.

  cpp.spec "TestCounting()" as test_counting with (\post emp).
  Lemma test_counting_ok : verify[source] test_counting.
  Proof using MOD.
    verify_spec. go.
    call_on_array a_addr 3%Z [1; 0; 2]%Z calls_addr
      (counting_call_ok calls_addr [1; 0; 2]%Z ltac:(done)).
  Qed.

  (** A function pointer: its model is the pointer. *)
  #[local] Instance fnptr_rep : BundledRep "bool(*)(int)" ptr :=
    {| objR q f := primR "bool(*)(int)" q (Vptr f) |}.
  #[local] Instance is_zero_pred : std.Predicate "bool(*)(int)" ptr Z :=
    std.pure_predicate (fun _ x => bool_decide (x = 0)%Z).

  cpp.spec "is_zero(int)" as is_zero_spec with
    (\arg{x} "x" (Vint x)
     \post[Vbool (bool_decide (x = 0)%Z)] emp).

  Lemma is_zero_ok : verify[source] is_zero_spec.
  Proof using MOD. verify_spec. go. Qed.

  Lemma is_zero_call_ok xs :
    denoteModule source ⊢ □ emp -∗
      std.predicate_call true (Tptr "int") "bool(*)(int)" (fun q x => intR q x)
        (_global "is_zero(int)") xs.
  Proof using MOD. std.verify_predicate_call is_zero_ok. Qed.

  cpp.spec "TestFunctionPointer()" as test_function_pointer with (\post emp).
  Lemma test_function_pointer_ok : verify[source] test_function_pointer.
  Proof using MOD.
    verify_spec. go.
    call_on_array a_addr 2%Z [0; 0]%Z tt (is_zero_call_ok [0; 0]%Z).
  Qed.

  (** A captureless closure: no state, so its model is [unit]. *)
  #[local] Instance lambda_rep : BundledRep lambda_ty unit :=
    {| objR q _ := structR lambda_name q |}.
  #[local] Instance lambda_pred : std.Predicate lambda_ty unit Z :=
    std.pure_predicate (fun _ x => bool_decide (x > 5)%Z).

  Definition lambda_spec : mpred :=
    specify
      {| info_name := Nscoped lambda_name (Nop function_qualifiers.Nc OOCall [Tint]);
         info_type := tMethod lambda_name QC Tbool [Tint] |}
      (fun this : ptr =>
        \arg{x} "x" (Vint x)
        \prepost{q} this |-> structR lambda_name q
        \post[Vbool (bool_decide (x > 5)%Z)] emp).

  Lemma lambda_ok : verify[source] lambda_spec.
  Proof using MOD. rewrite /lambda_spec. verify_spec. go. Qed.

  (** The copy of [big] passed by value. *)
  Definition lambda_copy_spec : mpred :=
    specify
      {| info_name := Nscoped lambda_name (Nctor [Tref (Tconst lambda_ty)]);
         info_type := tCtor lambda_name [Tref (Tconst lambda_ty)] |}
      (fun this : ptr =>
        \arg{other : ptr} "" (Vptr other)
        \prepost{q} other |-> structR lambda_name q
        \post this |-> structR lambda_name 1$m).

  Lemma lambda_copy_ok : verify[source] lambda_copy_spec.
  Proof using MOD. rewrite /lambda_copy_spec. verify_spec. go. Qed.

  Definition lambda_dtor_spec : mpred :=
    specify
      {| info_name := Nscoped lambda_name Ndtor;
         info_type := tDtor lambda_name |}
      (fun this : ptr =>
        \pre this |-> structR lambda_name 1$m
        \post emp).

  Lemma lambda_dtor_ok : verify[source] lambda_dtor_spec.
  Proof using MOD. rewrite /lambda_dtor_spec. verify_spec. go. Qed.

  Lemma lambda_call_ok p xs :
    denoteModule source ⊢ □ emp -∗
      std.predicate_call false (Tptr "int") lambda_ty (fun q x => intR q x) p xs.
  Proof using MOD. std.verify_predicate_call lambda_ok. Qed.

  (** The closure's copy constructor and destructor are stated with [specify], so
      [verify_spec] does not find them: [verify?] only warns, and the proof poses
      them from the module. *)
  cpp.spec "TestLambda()" as test_lambda with (\post emp).
  Lemma test_lambda_ok : verify?[source] test_lambda.
  Proof using MOD.
    verify_spec. go.
    iRename select (denoteModule _) into "Hmodule".
    iPoseProof (lambda_copy_ok with "Hmodule") as "#Hcopy".
    iPoseProof (lambda_dtor_ok with "Hmodule") as "#Hdtor".
    go $usenamed=true.
    call_on_array a_addr 2%Z [1; 2]%Z tt (lambda_call_ok tt [1; 2]%Z).
    go $usenamed=true.
    call_on_array a_addr 2%Z [1; 2]%Z tt (lambda_call_ok tt [1; 2]%Z).
    go $usenamed=true.
  Qed.

  Definition test_all_of_B := [LINK] test_all_of_ok.
  Definition test_any_of_B := [LINK] test_any_of_ok.
  Definition test_none_of_B := [LINK] test_none_of_ok.
  Definition test_function_pointer_B := [LINK] test_function_pointer_ok.
  Definition test_counting_B := [LINK] test_counting_ok.
  Definition test_lambda_B := [LINK] test_lambda_ok.
  Definition positive_B := [LINK] positive_ok.
  Definition counting_B := [LINK] counting_ok.
  Definition is_zero_B := [LINK] is_zero_ok.
  #[local] Hint Resolve test_all_of_B test_any_of_B test_none_of_B
    test_function_pointer_B test_counting_B test_lambda_B positive_B counting_B is_zero_B : sl_opacity.

  cpp.spec "main()" as main_spec with (\post[Vint 0] emp).

  Lemma main_ok : verify[source] main_spec.
  Proof using MOD. verify_spec. go. Qed.
  Definition main_B := [LINK] main_ok.
  #[local] Hint Resolve main_B : sl_opacity.

  (** All the proofs above, linked against the three algorithm specifications. *)
  Lemma specs_ok :
    denoteModule source **
    ▷ ( std.all_of_spec (Tptr "int") "Positive" source **
        std.all_of_spec (Tptr "int") "bool(*)(int)" source **
        std.all_of_spec (Tptr "int") "CountingPositive" source **
        std.any_of_spec (Tptr "int") "Positive" source **
        std.none_of_spec (Tptr "int") "Positive" source **
        std.any_of_spec (Tptr "int") lambda_ty source **
        std.none_of_spec (Tptr "int") lambda_ty source **
        std.cassert.specs )
    |-- main_spec.
  Proof using MOD.
    rewrite /std.cassert.specs.
    iIntros "[#? #(? & ? & ? & ? & ? & ? & ? & ? & ?)]".
    work.
  Qed.
End with_cpp.
