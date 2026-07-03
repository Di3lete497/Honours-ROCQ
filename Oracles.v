From Coq Require Import Bool List.
Import ListNotations.

Require Import DJ.BitStrings.
Require Import DJ.BooleanFunctions.

(*************************************************************)
(* Constant Oracles                                          *)
(*************************************************************)

Definition constant_zero : Oracle :=
  fun _ => false.

Definition constant_one : Oracle :=
  fun _ => true.

(*************************************************************)
(* Linear Oracles                                            *)
(*************************************************************)

Definition oracle_first_bit : Oracle :=
  first_bit.

Definition oracle_parity : Oracle :=
  parity.

Definition oracle_full_parity : Oracle :=
  parity.

Definition oracle_xor_two_bits : Oracle :=
  xor_two_bits.

(*************************************************************)
(* Affine Oracle                                             *)
(*************************************************************)
Definition oracle_affine : Oracle :=
  affine.

(*************************************************************)
(* Simple Nonlinear Oracle                                   *)
(*************************************************************)

Definition oracle_and_xor : Oracle :=
  fun x =>

    andb
      (first_bit x)
      (parity x).

(*************************************************************)
(* Placeholder Random Oracle                                 *)
(* (Used only for experimentation.)                          *)
(*************************************************************)

Definition oracle_example_balanced : Oracle :=
  negb ∘ parity.

(*************************************************************)
(* Invalid Oracles                                           *)
(*************************************************************)

Definition oracle_single_marked : Oracle :=
  fun _ => false. (* Placeholder for marked-state oracle later *)

Definition oracle_majority : Oracle :=
  majority.

Definition oracle_alternating : Oracle :=
  alternating.

(* Later proved:

Theorem first_bit_balanced :
    Balanced oracle_first_bit.

*)