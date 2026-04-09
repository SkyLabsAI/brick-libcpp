(*
 * Copyright (c) 2025 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.

Require Export skylabs.brick.libstdcpp.ctime.pred.
Require Import skylabs.brick.libstdcpp.ctime.inc_ctime_cpp.

#[local] Set Primitive Projections.
#[local] Open Scope Z_scope.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  cpp.spec (named "clock") with
    (\post{ticks}[Vint ticks]
      [| clock_result ticks \/ ticks = -1 |]).

  cpp.spec (named "time") with
    (\arg{timer_p} "__timer" (Vptr timer_p)
     \pre if bool_decide (timer_p = nullptr) then emp
          else timer_p |-> anyR Tlong 1$m
     \post{t}[Vint t]
       [| 0 <= t |] **
       later_than (abs_time_of_N (Z.to_N t)) **
       if bool_decide (timer_p = nullptr) then emp
       else timer_p |-> primR Tlong 1$m (Vint t)).

  cpp.spec (named "timespec_get") with
    (\arg{ts_p} "__ts" (Vptr ts_p)
     \arg{base} "__base" (Vint base)
     \pre ts_p |-> anyR "timespec" 1$m
     \post{r}[Vint r]
       if bool_decide (base = TIME_UTC /\ r = TIME_UTC) then
         Exists ts,
           [| timespec_get_result ts |] **
           [| 0 <= timespec_model_nsec ts < 1000000000 |] **
           ts_p |-> timespecR 1$m ts
       else
         [| r = 0 |] **
         ts_p |-> anyR "timespec" 1$m).

  cpp.spec (named "mktime") with
    (\arg{tm_p} "__tp" (Vptr tm_p)
     \prepost{q tm_in} tm_p |-> tmR q tm_in
     \post{t}[Vint t]
       Exists tm_out,
         [| mktime_result tm_in tm_out t |] **
         tm_p |-> tmR q tm_out).

  cpp.spec (named "gmtime") with
    (\arg{timer_p} "__timer" (Vptr timer_p)
     \prepost{q t} timer_p |-> primR Tlong q (Vint t)
     \post{res qret}[Vptr res]
       if bool_decide (res = nullptr) then emp
       else Exists tm,
         [| utc_time_to_tm t tm |] **
         res |-> tmR (cQp.const qret) tm **
         □ (Forall (qret' : Qp),
             res |-> tmR (cQp.const qret') tm ={⊤}=∗ emp)).

  cpp.spec (named "localtime") with
    (\arg{timer_p} "__timer" (Vptr timer_p)
     \prepost{q t} timer_p |-> primR Tlong q (Vint t)
     \post{res qret}[Vptr res]
       if bool_decide (res = nullptr) then emp
       else Exists tm,
         [| local_time_to_tm t tm |] **
         res |-> tmR (cQp.const qret) tm **
         □ (Forall (qret' : Qp),
             res |-> tmR (cQp.const qret') tm ={⊤}=∗ emp)).

  cpp.spec (named "asctime") with
    (\arg{tm_p} "__tp" (Vptr tm_p)
     \prepost{q tm} tm_p |-> tmR q tm
     \post{res qret}[Vptr res]
       if bool_decide (res = nullptr) then emp
       else Exists out,
         [| asctime_text_of tm out |] **
         [| cstring.size out = 25 |] **
         res |-> cstring.R (cQp.const qret) out **
         □ (Forall (qret' : Qp),
             res |-> cstring.R (cQp.const qret') out ={⊤}=∗ emp)).

  cpp.spec (named "ctime") with
    (\arg{timer_p} "__timer" (Vptr timer_p)
     \prepost{q t} timer_p |-> primR Tlong q (Vint t)
     \post{res qret}[Vptr res]
       if bool_decide (res = nullptr) then emp
       else Exists out,
         [| ctime_text_of t out |] **
         [| cstring.size out = 25 |] **
         res |-> cstring.R (cQp.const qret) out **
         □ (Forall (qret' : Qp),
             res |-> cstring.R (cQp.const qret') out ={⊤}=∗ emp)).

  cpp.spec (named "strftime") with
    (\arg{buf_p} "__s" (Vptr buf_p)
     \arg{maxsize} "__maxsize" (Vn maxsize)
     \arg{format_p} "__format" (Vptr format_p)
     \arg{tm_p} "__tp" (Vptr tm_p)
     \prepost{buf_in} buf_p |-> cstring.bufR 1 (Z.of_N maxsize) buf_in
     \prepost{qfmt format_s} format_p |-> cstring.R qfmt format_s
     \prepost{qtm tm} tm_p |-> tmR qtm tm
     \post{written}[Vn written]
       if bool_decide (written = 0)%N then
         Exists buf_out,
           buf_p |-> cstring.bufR 1 (Z.of_N maxsize) buf_out
       else Exists out,
         [| strftime_text_of format_s tm out |] **
         [| 0 <= cstring.size out < Z.of_N maxsize |] **
         [| written = Z.to_N (cstring.size out) |] **
         buf_p |-> cstring.bufR 1 (Z.of_N maxsize) out).

  (* BRiCk does not currently support doubles, so [difftime] is deferred. *)

End with_cpp.
