(*************************************************************)
(* DJTests.v                                                 *)
(*                                                           *)
(* Basic tests for the Deutsch-Jozsa verification framework. *)
(*************************************************************)

From Coq Require Import List Bool Arith Lia Classical.
Import ListNotations.

Require Import DJ.Foundations.BitStrings.
Require Import DJ.Foundations.Enumeration.
Require Import DJ.Foundations.Counting.

Require Import DJ.Oracles.BooleanFunctions.
Require Import DJ.Oracles.Oracles.
Require Import DJ.Oracles.Promise.

Require Import DJ.Verification.Balanced.
Require Import DJ.Verification.OracleProofs.

Require Import DJ.DeutschJozsa.DJ.
Require Import DJ.DeutschJozsa.DJProofs.

(*************************************************************)
(* Basic BitString Tests                                     *)
(*************************************************************)

Example count_ones_test :
  count_ones [true; false; true; true] = 3.
Proof.
  reflexivity.
Qed.

Example constant_zero_test :
  forall x,
    constant_zero x = false.
Proof.
  apply constant_zero_evaluates.
Qed.

Example parity_test :
  parity [true; true] = false.
Proof.
  reflexivity.
Qed.

Example first_bit_test :
  first_bit [true; false; false] = true.
Proof.
  reflexivity.
Qed.

Example last_bit_test :
  last_bit [true; false; true] = true.
Proof.
  reflexivity.
Qed.

(*************************************************************)
(* Enumeration Tests                                         *)
(*************************************************************)

Example enumerate_zero_bits :
  enumerate_bitstrings 0 = [[]].
Proof.
  reflexivity.
Qed.

(*************************************************************)
(* Counting Tests                                            *)
(*************************************************************)

Example count_true_test :
  count_true [true; false; true; true] = 3.
Proof.
  reflexivity.
Qed.

Example count_false_test :
  count_false [true; false; true; true] = 1.
Proof.
  reflexivity.
Qed.

(*************************************************************)
(* Oracle Evaluation                                         *)
(*************************************************************)

Example evaluate_parity :
  evaluate parity [true; false] = parity [true; false].
Proof.
  reflexivity.
Qed.

Example evaluate_affine :
  evaluate affine [true; true] = affine [true; true].
Proof.
  reflexivity.
Qed.

(*************************************************************)
(* Promise Lemmas                                            *)
(*************************************************************)

Example promise_partition_test :
  forall n f,
    PromiseHolds n f \/ PromiseFails n f.
Proof.
  apply promise_partition.
Qed.

Example promise_or_invalid_test :
  forall n f,
    DJPromise n f \/ Invalid n f.
Proof.
  apply promise_or_invalid.
Qed.

Example invalid_is_undefined_test :
  forall n f,
    PromiseFails n f ->
    UndefinedBehaviour n f.
Proof.
  apply invalid_is_undefined.
Qed.

(*************************************************************)
(* Generic Logical Tests                                     *)
(*************************************************************)

Example promise_implies_not_invalid :
  forall n f,
    PromiseHolds n f ->
    ~ PromiseFails n f.
Proof.
  apply promise_implies_defined.
Qed.

Example promise_cases_test :
  forall n f,
    DJPromise n f <->
    Constant n f \/ Balanced n f.
Proof.
  apply promise_cases.
Qed.

(*************************************************************)
(* Compute Examples                                          *)
(*************************************************************)

Compute count_ones [true; false; true; true].

Compute count_zeros [true; false; true; true].

Compute parity [true; false; true].

Compute first_bit [true; false].

Compute last_bit [true; false; true].

Compute enumerate_bitstrings 3.

Compute count_true [true; false; true; false].

Compute count_false [true; false; true; false].
