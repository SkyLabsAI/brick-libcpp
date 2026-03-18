Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.iostream.spec.

Require Import skylabs.brick.libstdcpp.test.geeks_for_geeks_examples.N5_swap_cpp.

Import linearity.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "main()" from source as main_spec with (
    \prepost{osM} _global "std::cout" |-> ostreamR 1$m osM
    \pre{str} _global "std::cout" |-> ostream_contentR 1$m str
    \post[Vint 0]
      _global "std::cout" |-> ostream_contentR 1$m
        (str ++
        "Before swapping a = " ++
        Z_to_string 2 ++ " , b = " ++ Z_to_string 3 ++ "\n" ++
        "After swapping a = " ++ Z_to_string 3 ++ " , b = " ++ Z_to_string 2 ++ "\n"
      )
  ).

  Lemma main_ok : verify[source] "main()".
  Proof.
    verify_spec.
    go.

    iExists _, _.
    go.
    iExists _, _.
    go.
(*
Mode: expert
Status: ok
File: /workspaces/agent-foundation/brick-libcpp/rocq-brick-libstdcpp/test/geeks_for_geeks_examples/N5_swap.v
Locator: Lemma:main_ok
Failed command: <none>
Stuck reason: <not provided>

Current goal:

thread_info : biIndex
_Σ : gFunctors
Σ : cpp_logic thread_info _Σ
σ : genv
_H_ : source ⊧ σ
_PostPred_ : ptr → mpred
osM : ostreamT
str : cstring.t
PostCond : PostCondition
a_addr : ptr
_x_ : valid<"int"> 2
b_addr, _x_1, _x_4 : ptr
GUARDS : GWs.GUARDS
_x_0 : valid<"int"> 3
_x_2 : Qp
_x_3 : cstring.WF "Before swapping a = "
_x_5 : Qp
_x_6 : cstring.WF " , b = "
============================
_ : denoteModule source
_ : ostream_print_int_spec
_ : ostream_insert_string_spec
_ : ostream_insert_spec
_ : endl_spec
_ : type_ptr "int" a_addr
_ : type_ptr "int" b_addr
_ : type_ptr "char" _x_1
_ : ∀ q : Qp, _x_1 |-> cstring.R q$c "Before swapping a = " ={⊤}=∗ emp
_ : type_ptr "char" _x_4
_ : ∀ q : Qp, _x_4 |-> cstring.R q$c " , b = " ={⊤}=∗ emp
--------------------------------------□
_ : PostCond
_ : _x_1 |-> cstring.R _x_2$c "Before swapping a = "
_ : a_addr |-> intR 1$m 2
_ : _x_4 |-> cstring.R _x_5$c " , b = "
_ : b_addr |-> intR 1$m 3
--------------------------------------∗
∃ (state_f : ostreamT → ostreamT) (stream_f : cstring.t → cstring.t),
  _global
    "std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)"
  |-> cptrR
        (unmaterialized_fspec (tFunction ostream_cpp_type [ostream_cpp_type])
           (add_with
              (λ osP : ptr,
                 add_arg (Vptr osP)
                   (add_with
                      (λ osM0 : ostreamT,
                         add_pre (osP |-> ostreamR 1$m osM0)
                           (add_post (osP |-> ostreamR 1$m (state_f osM0))
                              (add_with
                                 (λ str0 : cstring.t,
                                    add_pre
                                      (osP |-> ostream_contentR 1$m str0)
                                      (start_post_list
                                         (DONE (Vptr osP)
                                            (osP
                                             |-> ostream_contentR 1$m
                                                 (stream_f str0)))))
                                 "str" DummyValue)))
                      "osM" DummyValue))
              "osP" DummyValue)) ∗
  (_global "std::cout" |-> ostreamR 1$m (state_f osM) ∗
   _global "std::cout"
   |-> ostream_contentR 1$m
         (stream_f
            ((((str ++ "Before swapping a = ") ++ Z_to_string 2) ++ " , b = ") ++
             Z_to_string 3)%bs) -∗
   interp source 1
     (interp source
        ((1 >*> 1) >*>
         ((1 >*> 1) >*> ((1 >*> 1) >*> ((1 >*> 1) >*> ((1 >*> 1) >*> 1)))))
        (wp_block source
           [region: "b" @ b_addr; "a" @ a_addr; return {?: "int"}]
           [Sdecl [Dvar "temp" "int" None];
            Sexpr
              (Eassign (Evar "temp" "int") (Ecast Cl2r (Evar "a" "int"))
                 "int");
            Sexpr
              (Eassign (Evar "a" "int") (Ecast Cl2r (Evar "b" "int")) "int");
            Sexpr
              (Eassign (Evar "b" "int") (Ecast Cl2r (Evar "temp" "int"))
                 "int");
            Sexpr
              (Eoperator_call OOLessLess
                 (operator_impl.MFunc
                    "std::basic_ostream<char, std::char_traits<char>>::operator<<(std::basic_ostream<char, std::char_traits<char>>&(* )(std::basic_ostream<char, std::char_traits<char>>&))"%cpp_name
                    Direct
                    "std::basic_ostream<char, std::char_traits<char>>&(std::basic_ostream<char, std::char_traits<char>>&(* )(std::basic_ostream<char, std::char_traits<char>>&))"%cpp_type)
                 [Eoperator_call OOLessLess
                    (operator_impl.MFunc
                       "std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"%cpp_name
                       Direct
                       "std::basic_ostream<char, std::char_traits<char>>&(int)"%cpp_type)
                    [Eoperator_call OOLessLess
                       (operator_impl.Func
                          "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char* )"%cpp_name
                          "std::basic_ostream<char, std::char_traits<char>>&(std::basic_ostream<char, std::char_traits<char>>&, const char* )"%cpp_type)
                       [Eoperator_call OOLessLess
                          (operator_impl.MFunc
                             "std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"%cpp_name
                             Direct
                             "std::basic_ostream<char, std::char_traits<char>>&(int)"%cpp_type)
                          [Eoperator_call OOLessLess
                             (operator_impl.Func
                                "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char* )"%cpp_name
                                "std::basic_ostream<char, std::char_traits<char>>&(std::basic_ostream<char, std::char_traits<char>>&, const char* )"%cpp_type)
                             [Eglobal "std::cout"
                                "std::basic_ostream<char, std::char_traits<char>>";
                              Ecast Carray2ptr
                                (Estring
                                   {|
                                     literal_string.bytes :=
                                       "After swapping a = ";
                                     literal_string.bytes_per_char := 1
                                   |} "char")];
                           Ecast Cl2r (Evar "a" "int")];
                        Ecast Carray2ptr
                          (Estring
                             {|
                               literal_string.bytes := " , b = ";
                               literal_string.bytes_per_char := 1
                             |} "char")];
                     Ecast Cl2r (Evar "b" "int")];
                  Ecast Cfun2ptr
                    (Eglobal
                       "std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)"
                       "std::basic_ostream<char, std::char_traits<char>>&(std::basic_ostream<char, std::char_traits<char>>&)")]);
            Sreturn (Some (Eint 0 "int"))]
           (Kfree source
              ((1 >*> FreeTemps.delete "int" b_addr) >*>
               FreeTemps.delete "int" a_addr)
              (Kcleanup source [] (Kreturn (λ v : ptr, ▷ _PostPred_ v)))))))

Commands tried:
- [ok] verify_spec.
- [ok] go.


Expert question:
I replayed this proof and the goal stopped changing. Which structural proof step, framing step, or lemma is missing here?
*)
Admitted.
End with_cpp.
