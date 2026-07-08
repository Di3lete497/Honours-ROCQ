From Coq Require Import Bool List.
Import ListNotations.

Require Import DJ.Foundations.BitStrings.
Require Import DJ.Oracles.BooleanFunctions.
Require Import DJ.Verification.Balanced.

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
  parity. (*Meant to be identical to oracle_parity, but with a different name for clarity in proofs.*)

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
(* Example Balanced Oracle                                  *)
(*************************************************************)

Definition oracle_example_balanced : Oracle :=
  fun x =>
    negb (parity x).

(*************************************************************)
(* Invalid Oracles                                           *)
(*************************************************************)
Definition oracle_single_marked : Oracle :=
  fun x =>
    bitstring_eqb x (all_ones (bit_length x)).

Definition oracle_majority : Oracle :=
  majority.

Definition oracle_alternating : Oracle :=
  alternating.

(* Later proved:

Theorem first_bit_balanced :
    Balanced oracle_first_bit.

*)

(*************************************************************)
(* Lemma                                                     *)
(*************************************************************)
Lemma constant_zero_evaluates :

forall x,

constant_zero x = false.

Proof.

reflexivity.

Qed.

Lemma constant_one_evaluates :

forall x,

constant_one x = true.

Proof.

reflexivity.

Qed.

Lemma parity_oracle_correct :

forall x,

oracle_parity x = parity x.

Proof.

reflexivity.

Qed.

Lemma first_bit_oracle_correct :

forall x,

oracle_first_bit x = first_bit x.

Proof.

reflexivity.

Qed.

Lemma affine_oracle_correct :

forall x,

oracle_affine x = affine x.

Proof.

reflexivity.

Qed.