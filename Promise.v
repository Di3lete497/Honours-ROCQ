(*************************************************************)
(* Deutsch-Jozsa Promise Specification                       *)
(*************************************************************)

From Coq Require Import Bool List.

Import ListNotations.

Require Import DJ.BitStrings.
Require Import DJ.BooleanFunctions.

Require Import Balanced.
Require Import Oracles.

(*************************************************************)
(* Promise Satisfaction                                      *)
(*************************************************************)

Definition PromiseSatisfied
           (f : Oracle)
           : Prop :=

  DJPromise f.

Definition PromiseViolated
           (f : Oracle)
           : Prop :=

  ~ DJPromise f.

(*************************************************************)
(* Expected Measurement Outcomes                             *)
(*************************************************************)

Definition OutputZero
           (b : BitString)
           : Prop :=

  b = all_zeros (length b).

Definition OutputNonZero
           (b : BitString)
           : Prop :=

  b <> all_zeros (length b).

(*************************************************************)
(* Deutsch-Jozsa Specification                               *)
(*************************************************************)

Definition DJSpecification
           (f : Oracle)
           (result : BitString)
           : Prop :=

  (Constant f -> OutputZero result)
/\
  (Balanced f -> OutputNonZero result).

(*************************************************************)
(* Correctness Predicate                                     *)
(*************************************************************)

Definition DJCorrect
           (f : Oracle)
           (result : BitString)
           : Prop :=

  PromiseSatisfied f
  /\
  DJSpecification f result.

(*************************************************************)
(* Promise Violation Behaviour                               *)
(*************************************************************)

Definition UndefinedBehaviour
           (f : Oracle)
           : Prop :=

  PromiseViolated f.


(*************************************************************)
(* Generic Lemmas                                            *)
(*************************************************************)

Lemma promise_partition :

  forall (f : Oracle),

  PromiseSatisfied f \/
  PromiseViolated f.
Proof.
Admitted.

Lemma constant_correctness :

  forall f result,

  Constant f ->

  OutputZero result ->

  DJCorrect f result.
Proof.
Admitted.

Lemma balanced_correctness :

  forall f result,

  Balanced f ->

  OutputNonZero result ->

  DJCorrect f result.
Proof.
Admitted.

Lemma invalid_is_undefined :

  forall f,
  
  PromiseViolated f ->

  UndefinedBehaviour f.
Proof.
Admitted.