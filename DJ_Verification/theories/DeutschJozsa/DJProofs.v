(*************************************************************)
(* Correctness Proofs for the Deutsch-Jozsa Algorithm        *)
(*************************************************************)

From Coq Require Import Bool List Arith Lia Classical.

Import ListNotations.

Require Import DJ.Foundations.BitStrings.

Require Import DJ.Oracles.BooleanFunctions.
Require Import DJ.Oracles.Oracles.

Require Import DJ.Verification.Balanced.
Require Import DJ.Oracles.Promise.
Require Import DJ.Verification.OracleProofs.

Require Import DJ.DeutschJozsa.DJ.

(*************************************************************)
(* Correctness for Constant Oracles                          *)
(*************************************************************)

Theorem DJ_constant_correct :

  forall n (f : Oracle),

  Constant n f ->

  DJAccepts f n.

Proof.
Admitted.

(*************************************************************)
(* Correctness for Balanced Oracles                          *)
(*************************************************************)

Theorem DJ_balanced_correct :

  forall n (f : Oracle),

  Balanced n f ->

  DJRejects f n.
Proof.
Admitted.

(*************************************************************)
(* Overall Correctness                                       *)
(*************************************************************)

Theorem DJ_correct :

  forall n (f : Oracle),

  DJPromise n f ->

  DJAlgorithmCorrect n f.

Proof.

  intros n f Hpromise.

  unfold DJAlgorithmCorrect.

  split.

  - intro Hconstant.

    apply DJ_constant_correct.

    exact Hconstant.

  - intro Hbalanced.

    apply DJ_balanced_correct.

    exact Hbalanced.

Qed.

(*************************************************************)
(* Verified Implications                                     *)
(*************************************************************)

Theorem verified_implies_promise :

  forall n f,

  DJVerified n f ->

  PromiseHolds n f.

Proof.

  intros n f Hverified.

  unfold DJVerified in Hverified.

  destruct Hverified as [Hpromise _].

  exact Hpromise.

Qed.

Theorem verified_implies_correct :

  forall n f,

  DJVerified n f ->

  DJAlgorithmCorrect n f.

Proof.

  intros n f Hverified.

  unfold DJVerified in Hverified.

  destruct Hverified as [_ Hcorrect].

  exact Hcorrect.

Qed.

Lemma promise_partition :

forall (n : nat) (f : Oracle),

PromiseHolds n f
\/
PromiseFails n f.

Proof.
  intros n f.

  unfold PromiseHolds.
  unfold PromiseFails.

  apply classic.

Qed.
(*************************************************************)
(* Verified Execution                                        *)
(*************************************************************)

Theorem DJ_verified_execution :

  forall n (f : Oracle),

  PromiseHolds n f ->

  DJVerified n f.
Proof.
Admitted.

(*************************************************************)
(* Example Oracles                                           *)
(*************************************************************)

Theorem constant_zero_verified :

  forall n,

  DJVerified n constant_zero.
Proof.
Admitted.

Theorem constant_one_verified :

  forall n,

  DJVerified n constant_one.
Proof.
Admitted.

Theorem first_bit_verified :

  forall n,

  DJVerified n oracle_first_bit.
Proof.
Admitted.

Theorem parity_verified :

  forall n,

  DJVerified n oracle_parity.
Proof.
Admitted.

Theorem full_parity_verified :

  forall n,

  DJVerified n oracle_full_parity.
Proof.
Admitted.

Theorem affine_verified :

  forall n,

  DJVerified n oracle_affine.
Proof.
Admitted.

(*************************************************************)
(* For Invalid Oracles                                       *)
(*************************************************************)
Theorem invalid_oracle_not_correct :

  forall n (f : Oracle) (result : BitString),

  PromiseFails n f ->

  ~ DJCorrect n f result.

Proof.

  intros n f result Hfail Hcorrect.

  unfold DJCorrect in Hcorrect.

  destruct Hcorrect as [Hpromise _].

  unfold PromiseFails in Hfail.

  unfold PromiseHolds in Hpromise.

  unfold Invalid in Hfail.

  apply Hfail.

  exact Hpromise.

Qed.

(*************************************************************)
(* Promise Violations                                        *)
(*************************************************************)

Theorem invalid_oracles_not_verified :

  forall n (f : Oracle),

  PromiseFails n f ->

  ~ DJVerified n f.
Proof.

  intros n f Hfail Hverified.

  unfold DJVerified in Hverified.

  destruct Hverified as [Hpromise _].

  unfold PromiseFails in Hfail.
  unfold PromiseHolds in Hpromise.
  unfold Invalid in Hfail.

  apply Hfail.

  exact Hpromise.

Qed.

(*************************************************************)
(* Soundness                                                 *)
(*************************************************************)

Theorem DJ_soundness :

  forall n (f : Oracle),

  DJVerified n f ->

  DJAlgorithmCorrect n f.
Proof.

  intros n f Hverified.

  unfold DJVerified in Hverified.

  destruct Hverified as [_ Hcorrect].

  exact Hcorrect.

Qed.


Theorem verified_has_promise :

forall n f,

DJVerified n f ->

DJPromise n f.

Proof.

  intros n f Hverified.

  unfold DJVerified in Hverified.

  destruct Hverified as [Hpromise _].

  unfold PromiseHolds in Hpromise.

  exact Hpromise.

Qed.
(*************************************************************)
(* Completeness                                              *)
(*************************************************************)

Theorem DJ_completeness :

  forall n (f : Oracle) (result : BitString),

  DJCorrect n f result ->

  PromiseHolds n f.
Proof.

  intros n f result Hcorrect.

  destruct Hcorrect as [Hpromise _].

  exact Hpromise.

Qed.

(*************************************************************)
(* Verified = TRUE Outcome                                   *)
(*************************************************************)
Theorem valid_oracle_verified :

  forall n (f : Oracle),

  DJPromise n f ->

  DJVerified n f.
Proof.
Admitted.

(*************************************************************)
(* Utility Lemmas                                            *)
(*************************************************************)
Lemma verified_destruct :

  forall n f,

  DJVerified n f

  ->

  PromiseHolds n f
  /\

  DJAlgorithmCorrect n f.

Proof.

  intros n f Hverified.

  unfold DJVerified in Hverified.

  exact Hverified.

Qed.

Lemma promise_or_invalid :

  forall n f,

  DJPromise n f

  \/

  Invalid n f.

Proof.

  intros n f.

  unfold Invalid.

  apply classic.

Qed.