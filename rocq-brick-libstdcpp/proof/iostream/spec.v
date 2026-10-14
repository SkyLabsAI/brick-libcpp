(**
Tentative iostreams specs.

These are trace-based specifications, and there is a _wish_ to move to a
different style of specifications.

*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.iostream.pred.
Require Export skylabs.brick.libstdcpp.iostream.itree_prop.

Require Import skylabs.brick.libstdcpp.iostream_trace.inc_iostream_cpp.

(*
Variant io_align : Set := left | right | internal.
Variant io_base : Set := dec | hex | oct.
Variant io_float : Set := fixed | scientific | hexfloat | defaultfloat.

Record ioflags : Set :=
{ boolalpha : bool
; showbase : bool
; showpoint : bool
; showpos : bool
; uppercase : bool
; align : io_align
; float : io_float
}.
*)

(* TODO: it probably makes sense to separate istream, ostream, and iomanip *)


Module ostream.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    (** Run the handler on each character in the string *)
    Fixpoint bs_dos (OS : Ostream) (bs : bs) (K : mpred) : mpred :=
      |={⊤}=>
      match bs with
      | BS.EmptyString => K
      | BS.String b bs => OS.(do) {[Write $ Byte.to_N b]} $ fun _ => bs_dos OS bs K
      end.
    #[global] Hint Opaque bs_dos : sl_opacity.
    Lemma bs_dos_fupd OS bs K : bs_dos OS bs K ⊣⊢ |={⊤}=> bs_dos OS bs K.
    Proof. by destruct bs => /=; rewrite fupd_idemp. Qed.

    #[global] Instance elim_modal_fupd_wp_lval E OS bs p P Q :
      ElimModal True p false (|={E}=> P) P (bs_dos OS bs Q) (bs_dos OS bs Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      rewrite {2}bs_dos_fupd. iIntros (?) "[>h k] !>"; iApply "k"; done.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval OS bs p P Q :
      ElimModal True p false (|==> P) P (bs_dos OS bs Q) (bs_dos OS bs Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_lval.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval OS bs P Q : AddModal (|={top}=> P) P (bs_dos OS bs Q).
    Proof.
      rewrite/AddModal.
      rewrite {2}bs_dos_fupd. iIntros "[>h k] !>"; iApply "k"; done.
    Qed.

    #[global]
    Instance bs_dos_proper_frame (OS: Ostream) b
      : kont.ProperFrame (T:=[tele]) (bs_dos OS b).
    Proof.
      constructor; intros.
      induction b; simpl.
      { iIntros "X >K !>"; iRevert "K"; iApply ("X" $! ()). }
      { iIntros "X". destruct OS.
        iIntros ">Y !>"; iRevert "Y".
        iApply (do_frame {[Write $ Byte.to_N b]}).(kont._frame).
        iIntros ([?[]]); simpl.
        iApply IHb. iAssumption. }
    Qed.

    #[global]
    Instance bs_dos_positive_proper_frame_eta (OS: Ostream) b
      : kont.ProperFrame (T:=[tele]) (fun x => bs_dos OS b x).
    Proof. apply bs_dos_proper_frame. Qed.

    cpp.spec "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char*)"
      from source as ostream_insert_spec with (
      \arg{osP} "" (Vptr osP)
      \prepost{OS γ} osP |-> ostream.R OS γ 1$m
      \arg{strP} "" (Vptr strP)
      \prepost{q__s strM} strP |-> cstring.R q__s strM
      \pre{Q} bs_dos OS strM Q
      \post[Vptr osP] Q).

    Parameter format_int : Z -> bs.
    #[global] Declare Instance format_int_inj : Inj eq eq format_int.
    (** TODO: find an implementation!*)

    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"
      from source as ostream_print_int_spec with (
      \this this
      \arg{n} "" (Vint n)
      \prepost{OS γ} this |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS (format_int n) Q
      \post[Vptr this] Q
    ).

    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(unsigned long)"
      from source as ostream_print_ulong_spec with (
      \this this
      \arg{n} "" (Vint n)
      \prepost{OS γ} this |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS (format_int n) Q
      \post[Vptr this] Q
    ).

    Definition iostream_manip_spec contents_f : WpSpec_cpp_val := (
      \arg{osP : ptr} "" (Vptr osP)
      (* XXX: manipulators can cause output! *)
      \prepost{OS γ} osP |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS contents_f Q
      \post[Vptr osP] Q).

    Definition ostream_cpp_type : type :=
      "std::basic_ostream<char, std::char_traits<char>>&".
    Definition iostream_manip_kind : okind :=
      tFunction ostream_cpp_type [ostream_cpp_type].

    cpp.spec "std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)"
      from source as endl_spec with (
      \exact Reduce iostream_manip_spec "
"%bs
    ).

    (* This is the overload taking the endl manipulator. *)
    (* https://eel.is/c++draft/output.streams#ostream.inserters *)
    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(std::basic_ostream<char, std::char_traits<char>>&(*)(std::basic_ostream<char, std::char_traits<char>>&))"
      from source as ostream_insert_string_spec with (
      \this this
      \arg{os_f} "" (Vptr os_f)
      \pre{spec} os_f |-> unmaterialized_specR iostream_manip_kind spec
      (* ^^ this would be *slightly* more general if it took a materialized specification *)
      \pre{Q} (spec [Vref this] (fun v => [| v = Vptr this |] ** Q))
      \post[Vptr this] Q
    ).


  End with_cpp.
End ostream.

Module istream.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    Variant input_char : Type -> Type :=
      | read : input_char N.

    Definition as_event (T : Type) (act : input_char T) : T -> input_event :=
      match act in input_char T return T -> _ with
      | read => fun n => Read n
      end.

    (** [is_ws] returns true if the character is a standard whitespace 
        (space, \n, \r, \t, \v, \f). *)
    Definition is_ws (c : N) : bool :=
      bool_decide (c = 32 \/ c = 10 \/ c = 13 \/ c = 9 \/ c = 11 \/ c = 12)%N.

    (** [as_digit] returns [Some d] if the character is between '0' and '9'.
        Uses stdpp's bool_decide to evaluate the logical conjunction. *)
    Definition as_digit (c : N) : option N :=
      if bool_decide (48 <= c /\ c <= 57)%N then
        Some (c - 48)%N
      else
        None.

    (** [read_int] reads characters using [Do read] and parses
        the string as an integer. For example, the characters
        <1>, <2>, <\n> would return <('\n', Some 12)>.

        The function accepts both positive and negative integers. It returns
        [None] if no digits precede the first other character (including after
        a sign), which is a conversion failure.

        The first component is the "overread", the first byte read that
        is not part of the number.
    *)
    CoFixpoint read_int : itree input_char (N * option Z) :=
      (* Internal state machine to accumulate parsed digits *)
      let cofix loop (sign : Z) (acc : Z) : itree input_char (N * option Z) :=
        Do read (fun c =>
          match as_digit c with
          | Some digit =>
            loop sign (acc * 10 + Z.of_N digit)%Z
          | None =>
            (* Not a digit: return the delimiter character and the final signed integer *)
            Ret (c, Some (sign * acc)%Z)
          end
        )
      in
      (* After a sign, at least one digit is required *)
      let signed (sign : Z) : itree input_char (N * option Z) :=
        Do read (fun c =>
          match as_digit c with
          | Some digit => loop sign (Z.of_N digit)
          | None => Ret (c, None)
          end)
      in

      Do read (fun c =>
        if (c =? 45)%N then
          (* Encountered '-' (ASCII 45) -> Start reading negative number *)
          signed (-1)%Z

        else if (c =? 43)%N then
          (* Encountered '+' (ASCII 43) -> Start reading positive number *)
          signed 1%Z

        else if is_ws c then
          (* Whitespace -> Co-recursively skip *)
          read_int

        else match as_digit c with
            | Some digit =>
                (* Encountered a digit -> Start accumulating a positive number *)
                loop 1%Z (Z.of_N digit)
            | None =>
                (* Unexpected character before any digits -> Conversion failure *)
                Ret (c, None)
            end
        ).

    (** [run_buf buf it] runs [it] on the characters [buf] first, each in an
        internal step, and returns the characters of [buf] left over. *)
    CoFixpoint run_buf {T} (buf : list N) (it : itree input_char T) : itree input_char (T * list N) :=
      match it with
      | Ret v => Ret (v, buf)
      | Tau it => Tau (run_buf buf it)
      | Do act k =>
          match buf with
          | [] => Do act (fun x => run_buf [] (k x))
          | c :: buf =>
              Tau (run_buf buf
                ((match act in input_char U return (U -> _) -> _ with
                  | read => fun k => k c
                  end) k))
          end
      end.

    #[local] Abbreviation int_min := (int_rank.min_val int_rank.Iint Signed).
    #[local] Abbreviation int_max := (int_rank.max_val int_rank.Iint Signed).

    (** Whether extracting [r], a result of [read_int], succeeds, and the
        value it stores: a conversion failure stores 0, and an out-of-range
        value the nearest [int] limit, and both set [failbit]
        ([facet.num.get.virtuals], [istream.formatted.arithmetic]). *)
    Definition int_ok (r : option Z) : bool :=
      match r with
      | Some n => bool_decide (int_min <= n <= int_max)%Z
      | None => false
      end.
    Definition int_stored (r : option Z) : Z :=
      match r with
      | Some n => Z.max int_min (Z.min int_max n)
      | None => 0
      end.

    (** [K ((c, r), buf')] continues after [read_int] returns [r] and the
        read-ahead [c], with [buf'] left over from the stream's characters.
        Extraction stops before [c] ([facet.num.get.virtuals] stage 2), which
        stays in the stream. [istream.R] does not model [failbit], so after a
        failed extraction the caller loses the stream: further extractions
        would do nothing. *)
    cpp.spec "std::basic_istream<char, std::char_traits<char>>::operator>>(int&)"
      from source as istream_take_int_spec with (
          \this this
          \pre{IS isM buf} this |-> istream.R IS isM buf 1$m
          \arg{nP} "" (Vref nP)
          \pre nP |-> anyR "int" 1$m
          \pre{K : (N * option Z) * list N -> mpred}
            interp_itree as_event IS (run_buf buf read_int) K
          \post[Vptr this] Exists isM' c r buf',
            nP |-> intR 1$m (int_stored r) ** K ((c, r), buf') **
            if int_ok r then this |-> istream.R IS isM' (c :: buf') 1$m else emp
        ).

    (** ** Streams with known contents *)

    (** [script remaining] delivers the characters of a known input, one per
        read: [remaining cs] owns the characters [cs] not read yet. *)
    #[program]
    Definition script (remaining : list N -> mpred) : Istream :=
      {| do evts K := ∃ c cs, remaining (c :: cs) ** [| Read c ∈ evts |] **
                       (remaining cs -∗ K (Read c)) |}%I.
    Next Obligation.
      intros remaining evts. constructor => K K'.
      iIntros "HK (%c & %cs & R & % & W)". iExists c, cs. iFrame "R %".
      iIntros "R". iApply ("HK" $! (TeleArgCons (f:=λ _ : input_event, TeleO) (Read c) tt)).
      by iApply "W".
    Qed.
    Next Obligation. solve_proper. Qed.

    (** [feed fuel it cs] runs [it] on the input [cs], in at most [fuel]
        steps, and returns its result and the input left over. *)
    Fixpoint feed {T} (fuel : nat) (it : itree input_char T) (cs : list N) : option (T * list N) :=
      match fuel with
      | O => None
      | S fuel =>
          match it with
          | Ret v => Some (v, cs)
          | Tau it => feed fuel it cs
          | Do act k =>
              match cs with
              | [] => None
              | c :: cs =>
                  (match act in input_char U return (U -> _) -> _ with
                   | read => fun k => feed fuel (k c) cs
                   end) k
              end
          end
      end.

    Lemma feed_sound remaining fuel {T} (it : itree input_char T) cs v rest K :
      feed fuel it cs = Some (v, rest) ->
      remaining cs ** (remaining rest -∗ K v) ⊢ interp_itree as_event (script remaining) it K.
    Proof.
      elim: fuel it cs => [//|fuel IH] it cs /=.
      rewrite interp_itree_unfold.
      destruct it as [v'|it|U act k].
      - move=> [<- <-]. iIntros "[R W]". by iApply "W".
      - move=> /IH {}IH. iIntros "H !>". by iApply IH.
      - destruct act, cs as [|c cs] => //= /IH {}IH.
        iIntros "[R W]". iExists c, cs. iFrame "R".
        iSplitR; [iPureIntro; rewrite elem_of_PropSet; eauto|].
        iIntros "R". iExists c. iSplitR; [done|]. iNext. iApply IH. iFrame.
    Qed.

    (** The automation proves an extraction from [script] by running it, and
        continues with its result.
        ponytail: at most 4096 steps (characters and buffered characters);
        longer runs are left to the user, via [feed_sound]. *)
    #[program]
    Definition feed_script_C remaining {T} (it : itree input_char T) cs v rest
        (_ : feed 4096 it cs =[Vm]=> Some (v, rest)) :=
      \cancelx
      \bound_existential (K : T -> mpred)
      \consuming remaining cs
      \proving interp_itree as_event (script remaining) it K
      \instantiate K := (λ x, [| x = v |] ** remaining rest)%I
      \end.
    Next Obligation.
      intros * Hfeed%RedEq_eq. iIntros "R" (K ->). iIntros (->).
      iApply (feed_sound remaining 4096 _ _ v rest _ Hfeed with "[$R]").
      iIntros "$". by iPureIntro.
    Qed.

  End with_cpp.
  #[export] Hint Resolve feed_script_C : br_hints.

End istream.
