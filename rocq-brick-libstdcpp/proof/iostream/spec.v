(**
Tentative iostreams specs.

These are trace-based specifications, and there is a _wish_ to move to a
different style of specifications.

*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.iostream.pred.

Require Import skylabs.brick.libstdcpp.iostream.inc_iostream_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  cpp.spec "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char*)" from source as ostream_insert_spec with (
    \arg{osP} "" (Vptr osP)
    \prepost{osM} osP |-> ostreamR 1$m osM
    \pre{str} osP |-> ostream_contentR 1$m str
    \arg{strP} "" (Vptr strP)
    \prepost{q__s strM} strP |-> cstring.R q__s strM
    \post[Vptr osP]
      osP |-> ostream_contentR 1$m (str ++ strM)).

  Parameter Z_to_string : Z -> cstring.t.
  #[global] Declare Instance Z_to_string_inj : Inj eq eq Z_to_string.
  (** TODO: find an implementation!*)

  cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(int)" from source as ostream_print_int_spec with (
    \this this
    \prepost{osM} this |-> ostreamR 1$m osM
    \pre{str} this |-> ostream_contentR 1$m str
    \arg{n} "" (Vint n)
    \post[Vptr this]
        this |-> ostream_contentR 1$m (str ++ Z_to_string n)
  ).

  cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(unsigned long)" from source as ostream_print_ulong_spec with (
    \this this
    \prepost{osM} this |-> ostreamR 1$m osM
    \pre{str} this |-> ostream_contentR 1$m str
    \arg{n} "" (Vint n)
    \post[Vptr this]
        this |-> ostream_contentR 1$m (str ++ Z_to_string n)
  ).

  Definition iostream_manip_spec state_f contents_f : WpSpec_cpp_val := (
    \arg{osP : ptr} "" (Vptr osP)
    (* XXX: manipulators can modify [osM]! *)
    \pre{osM} osP |-> ostreamR 1$m osM
    \post* osP |-> ostreamR 1$m (state_f osM)
    \pre{str} osP |-> ostream_contentR 1$m str
    \post[Vptr osP] osP |-> ostream_contentR 1$m (contents_f str)).

  Definition ostream_cpp_type : type :=
    "std::basic_ostream<char, std::char_traits<char>>&".
  Definition iostream_manip_kind : okind :=
    tFunction ostream_cpp_type [ostream_cpp_type].

  cpp.spec "std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)" from source as endl_spec with (
    \exact Reduce iostream_manip_spec (fun osM => osM) (fun str => str ++ "\n")%bs
  ).

  (* This is the overload taking the endl manipulator. *)
  (* https://eel.is/c++draft/output.streams#ostream.inserters *)
  cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(std::basic_ostream<char, std::char_traits<char>>&(*)(std::basic_ostream<char, std::char_traits<char>>&))"
    from source as ostream_insert_string_spec with (
    \this this
    \arg{os_f} "" (Vptr os_f)
    \pre{state_f stream_f}
      os_f |-> unmaterialized_specR
        iostream_manip_kind
        (iostream_manip_spec state_f stream_f)
    \pre{osM} this |-> ostreamR 1$m osM
    \post* this |-> ostreamR 1$m (state_f osM)
    \pre{str} this |-> ostream_contentR 1$m str
    \post[Vptr this]
      this |-> ostream_contentR 1$m (stream_f str)
  ).

  (** NOTE: this specification is weak because it does not connect to the
      actual stream "contents". *)
  cpp.spec "std::basic_istream<char, std::char_traits<char>>::operator>>(int&)"
    from source as istream_take_int_spec with (
    \this this
    \pre{isM} this |-> istreamR 1$m isM
    \arg{nP} "" (Vptr nP)
    \pre nP |-> anyR "int" 1$m
    \post[Vptr this] Exists isM' n,
        this |-> istreamR 1$m isM' **
          nP |-> intR 1$m n
  ).

End with_cpp.
