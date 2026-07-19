(*
1. Core Definitions (Binary32 / Single Precision)
To work with standard IEEE 754 Single Precision (binary32), we configure Flocq's
parameters with a precision of 24 bits (prec := 24) and an exponent maximum
bound of 149 (emax := 128).
*)
Require Import ZArith.
Require Import Bool.
(* Require Import Flocq.Appli.Fappli_IEEE. *)
Require Import Flocq.Core.Digits.
Require Import Flocq.IEEE754.Binary.

(* Define standard IEEE 754 binary32 parameters *)
Definition prec := 24%Z.
Definition emax := 128%Z.

(* Flocq's representation type for a valid NaN payload *)
(* The payload must strictly fit within (prec - 1) bits, which is 23 bits. *)


(*
2. Constructing a Quiet NaN (qNaN)
Per the IEEE 754 standard, a Quiet NaN has the most significant bit (MSB) of its
trailing significand set to 1. In a 23-bit fraction field, this corresponds to
the bit value 2²².In Coq, we can represent this bit pattern using positive
binary integers (positive).
*)

(* The MSB of a 23-bit payload field is 2^22 = 4194304 *)
Definition qnan_payload_value : positive := 4194304%positive.

(* Create the final Quiet NaN value (Positive sign, payload) *)
Definition quiet_nan_float : binary_float prec emax :=
  B754_nan prec emax false qnan_payload_value eq_refl.

(*
3. Constructing a Signaling NaN (sNaN)
A Signaling NaN has the MSB of its trailing significand set to 0, but the
remaining payload bits must contain at least one non-zero bit (as an all-zero
fraction specifies Infinity, not NaN). For instance, setting the lowest bit to 1
yields a valid sNaN pattern.
*)

(* Lowest bit set to 1, MSB is 0 *)
Definition snan_payload_value : positive := 1%positive.

(* Create the final Signaling NaN value *)
Definition signaling_nan_float : binary_float prec emax :=
  B754_nan prec emax false snan_payload_value eq_refl.


(*
4. Distinguishing Them Programmatically

Because Flocq treats all NaNs uniformly at the type level, you have to write a
custom decoder function to check whether a Flocq NaN is quiet or signaling. This
mirrors how physical floating-point units evaluate numbers at runtime.
*)

(* Check if the MSB bit is set to 1 *)
Definition is_quiet_nan_pl (val : positive) : bool :=
  (* Define the MSB barrier for a 24-bit precision float (23-bit payload) *)
  let msb_mask : Z := 4194304%Z in (* 2^22 *)
  Z.odd (Zpos val / msb_mask).

Definition is_quiet_nan (f : binary_float prec emax) : bool :=
  match f with
  | B754_nan _ _ _ val _ =>
    is_quiet_nan_pl val
  | _ => false (* Not a NaN at all *)
  end.

Definition is_signaling_nan (f : binary_float prec emax) : bool :=
  match f with
  | B754_nan _ _ _ val _ =>
    negb (is_quiet_nan_pl val)
  | _ => false
  end.
