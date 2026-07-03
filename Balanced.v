From Coq Require Import Arith Lia.

Require Import Counting.

(*************************************************************)
(* Constant Oracles                                          *)
(*************************************************************)

Definition Constant
           {n}
           (f : Oracle n)
           : Prop :=

  count_true_outputs f = 0 \/
  count_false_outputs f = 0.

(*************************************************************)
(* Balanced Oracles                                          *)
(*************************************************************)

Definition Balanced
           {n}
           (f : Oracle n)
           : Prop :=

  count_true_outputs f =
  count_false_outputs f.

(*************************************************************)
(* Almost Balanced                                           *)
(*************************************************************)

Definition AlmostBalanced
           {n}
           (k : nat)
           (f : Oracle n)
           : Prop :=

  balance_distance f = k.

(*************************************************************)
(* Oracle Bias                                               *)
(*************************************************************)

Definition Bias
           {n}
           (f : Oracle n)
           : nat * nat :=

  output_bias f.

(*************************************************************)
(* Promise Satisfaction                                      *)
(*************************************************************)

Definition DJPromise
           {n}
           (f : Oracle n)
           : Prop :=

  Constant f \/
  Balanced f.

(*************************************************************)
(* Invalid Oracle                                            *)
(*************************************************************)

Definition Invalid
           {n}
           (f : Oracle n)
           : Prop :=

  ~ DJPromise f.

(*************************************************************)
(* Helper Properties                                         *)
(*************************************************************)

Definition PerfectlyBalanced
           {n}
           (f : Oracle n)
           : Prop :=

  balance_distance f = 0.

Definition NearBalanced
           {n}
           (k : nat)
           (f : Oracle n)
           : Prop :=

  balance_distance f <= k.

Definition Biased
           {n}
           (f : Oracle n)
           : Prop :=

  ~ Balanced f.

(*************************************************************)
(* Basic Relationships                                       *)
(*************************************************************)

Lemma perfectly_balanced_is_balanced :

  forall n (f : Oracle n),

  PerfectlyBalanced f ->

  Balanced f.
Proof.
Admitted.

Lemma constant_not_balanced :

  forall n (f : Oracle n),

  Constant f ->

  ~ Balanced f.
Proof.
Admitted.

Lemma invalid_not_promise :

  forall n (f : Oracle n),

  Invalid f ->

  ~ DJPromise f.
Proof.
Admitted.

(* We're building the lemmas up later with a real proof but for now in development, we will leave as is*)