(*************************************************************)
(* Correctness Proofs for the Deutsch-Jozsa Algorithm        *)
(*************************************************************)

From Coq Require Import Bool List Arith Lia.

Import ListNotations.

Require Import DJ.BitStrings.
Require Import DJ.BooleanFunctions.
Require Import DJ.Balanced.
Require Import DJ.Oracles.
Require Import DJ.Promise.
Require Import DJ.DJ.
Require Import DJ.OracleProofs.

(*************************************************************)
(* Correctness for Constant Oracles                          *)
(*************************************************************)

Theorem DJ_constant_correct :

  forall (f : Oracle) (n : nat),

  Constant f ->

  DJAccepts f n.
Proof.
Admitted.

(*************************************************************)
(* Correctness for Balanced Oracles                          *)
(*************************************************************)

Theorem DJ_balanced_correct :

  forall (f : Oracle) (n : nat),

  Balanced f ->

  DJRejects f n.
Proof.
Admitted.

(*************************************************************)
(* Overall Correctness                                       *)
(*************************************************************)

Theorem DJ_correct :

  forall (f : Oracle) (n : nat),

  DJPromise f ->

  DJCorrect f n.
Proof.
Admitted.

(*************************************************************)
(* Verified Execution                                        *)
(*************************************************************)

Theorem DJ_verified_execution :

  forall (f : Oracle) (n : nat),

  PromiseSatisfied f ->

  DJVerified f n.
Proof.
Admitted.

(*************************************************************)
(* Example Oracles                                           *)
(*************************************************************)

Theorem constant_zero_verified :

  forall n,

  DJVerified constant_zero n.
Proof.
Admitted.

Theorem constant_one_verified :

  forall n,

  DJVerified constant_one n.
Proof.
Admitted.

Theorem first_bit_verified :

  forall n,

  DJVerified oracle_first_bit n.
Proof.
Admitted.

Theorem parity_verified :

  forall n,

  DJVerified oracle_parity n.
Proof.
Admitted.

Theorem full_parity_verified :

  forall n,

  DJVerified oracle_full_parity n.
Proof.
Admitted.

Theorem affine_verified :

  forall n,

  DJVerified oracle_affine n.
Proof.
Admitted.

(*************************************************************)
(* For Invalid Oracles                                       *)
(*************************************************************)
Theorem invalid_oracle_not_correct :

  forall (f : Oracle) (n : nat),

  PromiseViolated f ->

  ~ DJCorrect f n.
Proof.
Admitted.

(*************************************************************)
(* Promise Violations                                        *)
(*************************************************************)

Theorem invalid_oracles_not_verified :

  forall (f : Oracle) (n : nat),

  PromiseViolated f ->

  ~ DJVerified f n.
Proof.
Admitted.

(*************************************************************)
(* Soundness                                                 *)
(*************************************************************)

Theorem DJ_soundness :

  forall (f : Oracle) (n : nat),

  DJVerified f n ->

  DJCorrect f n.
Proof.
Admitted.

(*************************************************************)
(* Completeness                                              *)
(*************************************************************)

Theorem DJ_completeness :

  forall (f : Oracle) (n : nat),

  DJCorrect f n ->

  PromiseSatisfied f.
Proof.
Admitted.

(*************************************************************)
(* Robustness                                                *)
(*************************************************************)

Definition PromiseRobust
           (f : Oracle)
           : Prop :=

DJPromise f.

Theorem promise_violation_changes_behaviour :

  forall (f : Oracle) (n : nat),

  PromiseViolated f ->

  ~ DJVerified f n.
Proof.
Admitted.

(*************************************************************)
(* Verified = TRUE Outcome                                   *)
(*************************************************************)
Theorem valid_oracle_verified :

  forall (f : Oracle) (n : nat),

  DJPromise f ->

  DJVerified f n.
Proof.
Admitted.
