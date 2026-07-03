(*************************************************************)
(* Formal Properties of Example Oracle Families              *)
(*************************************************************)

From Coq Require Import Bool List Arith Lia.

Import ListNotations.

Require Import DJ.BitStrings.
Require Import DJ.BooleanFunctions.

Require Import Counting.
Require Import Balanced.
Require Import Oracles.

(*************************************************************)
(* Constant Oracles                                          *)
(*************************************************************)

Theorem constant_zero_is_constant :

  Constant constant_zero.
Proof.
  unfold Constant.
  left.
Admitted.

Theorem constant_one_is_constant :

  Constant constant_one.
Proof.
  unfold Constant.
  right.
Admitted.

(*************************************************************)
(* Balanced Oracles                                          *)
(*************************************************************)

Theorem first_bit_is_balanced :

  Balanced oracle_first_bit.
Proof.
Admitted.

Theorem parity_is_balanced :

  Balanced oracle_parity.
Proof.
Admitted.

Theorem full_parity_is_balanced :

  Balanced oracle_full_parity.
Proof.
Admitted.

Theorem xor_two_bits_is_balanced :

  Balanced oracle_xor_two_bits.
Proof.
Admitted.

(*************************************************************)
(* Affine Oracle                                             *)
(*************************************************************)

Theorem affine_is_balanced :

  Balanced oracle_affine.
Proof.
Admitted.

(*************************************************************)
(* Nonlinear Oracle                                          *)
(*************************************************************)

Theorem and_xor_is_not_constant :

  ~ Constant oracle_and_xor.
Proof.
Admitted.

(*************************************************************)
(* Invalid Oracles                                           *)
(*************************************************************)

Theorem majority_invalid :

  Invalid oracle_majority.
Proof.
Admitted.

Theorem single_marked_invalid :

  Invalid oracle_single_marked.
Proof.
Admitted.

(*************************************************************)
(* Promise Satisfaction                                      *)
(*************************************************************)

Theorem first_bit_satisfies_promise :

  DJPromise oracle_first_bit.
Proof.
  right.
  apply first_bit_is_balanced.
Qed.

Theorem parity_satisfies_promise :

  DJPromise oracle_parity.
Proof.
  right.
  apply parity_is_balanced.
Qed.

Theorem affine_satisfies_promise :

  DJPromise oracle_affine.
Proof.
  right.
  apply affine_is_balanced.
Qed.

Theorem constant_zero_satisfies_promise :

  DJPromise constant_zero.
Proof.
  left.
  apply constant_zero_is_constant.
Qed.

Theorem constant_one_satisfies_promise :

  DJPromise constant_one.
Proof.
  left.
  apply constant_one_is_constant.
Qed.

Theorem full_parity_satisfies_promise :

  DJPromise oracle_full_parity.
Proof.
  right.
  apply full_parity_is_balanced.
Qed.

(*************************************************************)
(* Generic Lemmas for Oracle Property Generalisation         *)
(*************************************************************)

Lemma balanced_implies_promise :
  forall (f : Oracle),
    Balanced f ->
    DJPromise f.
Proof.
Admitted.

Lemma constant_implies_promise :
  forall (f : Oracle),
    Constant f ->
    DJPromise f.
Proof.
Admitted.

Lemma invalid_not_promise :
  forall (f : Oracle),
    Invalid f ->
    ~ DJPromise f.
Proof.
Admitted.
(* Admitted is used currently but an actual proof will be added later *)