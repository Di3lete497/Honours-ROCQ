From Coq Require Import Arith Lia.

Require Import DJ.Foundations.Counting.
Require Import DJ.Oracles.BooleanFunctions.

(*************************************************************)
(* Balance Distance                                          *)

(*************************************************************)
(* Constant Oracles                                          *)
(*************************************************************)

Definition Constant
           (n : nat)
           (f : Oracle)
           : Prop :=

count_true_outputs f n = 0
\/
count_false_outputs f n = 0.

(*************************************************************)
(* Balanced Oracles                                          *)
(*************************************************************)

Definition Balanced
           (n : nat)
           (f : Oracle)
           : Prop :=

count_true_outputs f n =
count_false_outputs f n.

(*************************************************************)
(* Almost Balanced                                           *)
(*************************************************************)

Definition AlmostBalanced
           (n : nat)
           (k : nat)
           (f : Oracle)
           : Prop :=

  balance_distance f n = k.

(*************************************************************)
(* Oracle Bias                                               *)
(*************************************************************)

Definition OracleBias
           (n : nat)
           (f : Oracle)
           : nat * nat :=

output_ratio f n.

(*************************************************************)
(* Promise Satisfaction                                      *)
(*************************************************************)

Definition DJPromise
           (n : nat)
           (f : Oracle)
           : Prop :=

Constant n f
\/
Balanced n f.

(*************************************************************)
(* Invalid Oracle                                            *)
(*************************************************************)

Definition Invalid
           (n : nat)
           (f : Oracle)
           : Prop :=

~ DJPromise n f.

(*************************************************************)
(* Helper Properties                                         *)
(*************************************************************)

Definition PerfectlyBalanced
           (n : nat)
           (f : Oracle)
           : Prop :=

balance_distance f n = 0.

Definition NearBalanced
           (n : nat)
           (k : nat)
           (f : Oracle)
           : Prop :=

  balance_distance f n <= k.

Definition Biased
           (n : nat)
           (f : Oracle)
           : Prop :=

  ~ Balanced n f.


(*************************************************************)
(* Robustness Definitions                                    *)
(*************************************************************)
Definition PromiseDistance
           (n : nat)
           (f : Oracle)
           : nat :=

balance_distance f n.

Definition PromiseRobust
           (n : nat)
           (k : nat)
           (f : Oracle)
           : Prop :=

PromiseDistance n f <= k.

Definition PromiseViolated
           (n : nat)
           (f : Oracle)
           : Prop :=

PromiseDistance n f > 0.

(*************************************************************)
(* Basic Relationships                                       *)
(*************************************************************)
Lemma balanced_implies_promise :

forall n f,

Balanced n f ->

DJPromise n f.

Proof.

intros.

right.

assumption.

Qed.

Lemma constant_implies_promise :

forall n f,

Constant n f ->

DJPromise n f.

Proof.

intros.

left.

assumption.

Qed.

Lemma robust_zero :

forall n f,

PromiseRobust n 0 f

<->

Balanced n f.

Proof.
Admitted.

Lemma perfectly_balanced_is_balanced :

forall n (f : Oracle),

PerfectlyBalanced n f ->

Balanced n f.

Proof.
Admitted.

Lemma constant_not_balanced :

  forall n (f : Oracle),

  Constant n f ->

  ~ Balanced n f.
Proof.
Admitted.

Lemma invalid_not_promise :

forall n (f : Oracle),

Invalid n f ->

~ DJPromise n f.

Proof.

unfold Invalid.

firstorder.

Qed.

Lemma promise_implies_not_invalid :

forall n f,

DJPromise n f ->

~ Invalid n f.
Proof.

firstorder.

Qed.

Lemma invalid_equiv_not_promise :

forall n f,

Invalid n f <->

~ DJPromise n f.
Proof.

firstorder.

Qed.

(* We're building the lemmas up later with a real proof but for now in development, we will leave as is*)