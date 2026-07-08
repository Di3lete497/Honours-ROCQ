(*************************************************************)
(* Formal Properties of Example Oracle Families              *)
(*************************************************************)

From Coq Require Import Bool List Arith Lia.

Import ListNotations.

Require Import DJ.Foundations.BitStrings.
Require Import DJ.Foundations.Counting.
Require Import DJ.Foundations.Enumeration.

Require Import DJ.Oracles.BooleanFunctions.
Require Import DJ.Oracles.Oracles.
Require Import DJ.Oracles.Promise.

Require Import DJ.Verification.Balanced.

(*************************************************************)
(* Helper Lemmas                                             *)
(*************************************************************)
Lemma count_true_map_false :

forall (l : list BitString),

count_true (map (fun _ => false) l) = 0.

Proof.

induction l.

- reflexivity.

- simpl.
  rewrite IHl.
  reflexivity.

Qed.


Lemma count_true_map_true :

forall (l : list BitString),

count_true (map (fun _ => true) l) = length l.

Proof.

induction l.

- reflexivity.

- simpl.
  rewrite IHl.
  reflexivity.

Qed.

Lemma enumerate_bitstrings_length :

forall n,

length (enumerate_bitstrings n) = Nat.pow 2 n.

Proof.

Admitted. (*For constant 1, leave as admitted, it is an enumeration theorem, not oracle*)

(*************************************************************)
(* Constant Oracles                                          *)
(*************************************************************)

Theorem constant_zero_is_constant :

  forall n,

  Constant n constant_zero.
Proof.
  intro n.
  unfold Constant.
  left.

  unfold count_true_outputs.

  unfold oracle_outputs.

  unfold constant_zero.

  apply count_true_map_false.

Qed.

Theorem constant_one_is_constant :

  forall n,

  Constant n constant_one.
Proof.
  intro n.
  unfold Constant.
  right.

  unfold count_false_outputs.
  unfold count_true_outputs.
  unfold oracle_outputs.
  unfold enumerate_outputs.
  unfold constant_one.

  simpl.

  rewrite count_true_map_true.

  unfold number_of_inputs.

  rewrite enumerate_bitstrings_length.

  lia.
Qed.


(*************************************************************)
(* Balanced Oracles                                          *)
(*************************************************************)

Theorem first_bit_is_balanced :

  forall n,

  Balanced n oracle_first_bit.
Proof.
Admitted.

Theorem parity_is_balanced :

  forall n,

  Balanced n oracle_parity.
Proof.
Admitted.

Theorem full_parity_is_balanced :

  forall n,

  Balanced n oracle_full_parity.
Proof.
Admitted.

Theorem xor_two_bits_is_balanced :

  forall n,

  Balanced n oracle_xor_two_bits.
Proof.
Admitted.

(*************************************************************)
(* Affine Oracle                                             *)
(*************************************************************)

Theorem affine_is_balanced :

  forall n,

  Balanced n oracle_affine.
Proof.
Admitted.

(*************************************************************)
(* Nonlinear Oracle                                          *)
(*************************************************************)

Theorem and_xor_is_not_constant :

  forall n,

  ~ Constant n oracle_and_xor.
Proof.
Admitted.

(*************************************************************)
(* Invalid Oracles                                           *)
(*************************************************************)

Theorem majority_invalid :

  forall n,

  Invalid n oracle_majority.
Proof.
Admitted.

Theorem single_marked_invalid :

  forall n,
  Invalid n oracle_single_marked.
Proof.
Admitted.

(*************************************************************)
(* Promise Satisfaction                                      *)
(*************************************************************)

Theorem first_bit_satisfies_promise :

  forall n,
  DJPromise n oracle_first_bit.
Proof.
  intro n.

  right.

  apply (first_bit_is_balanced n).
Qed.

Theorem parity_satisfies_promise :

  forall n,
  DJPromise n oracle_parity.
Proof.
  intro n.
  right.
  apply (parity_is_balanced n).
Qed.

Theorem affine_satisfies_promise :

  forall n,
  DJPromise n oracle_affine.
Proof.
  intro n.
  right.
  apply (affine_is_balanced n).
Qed.

Theorem constant_zero_satisfies_promise :

  forall n,
  DJPromise n constant_zero.
Proof.
  intro n.
  left.
  apply (constant_zero_is_constant n).
Qed.

Theorem constant_one_satisfies_promise :

  forall n,
  DJPromise n constant_one.
Proof.
  intro n.
  left.
  apply (constant_one_is_constant n).
Qed.

Theorem full_parity_satisfies_promise :

  forall n,
  DJPromise n oracle_full_parity.
Proof.
  intro n.
  right.
  apply (full_parity_is_balanced n).
Qed.

(*************************************************************)
(* Generic Lemmas for Oracle Property Generalisation         *)
(*************************************************************)

Lemma affine_oracle_correct :

  forall x,

  oracle_affine x = affine x.

Proof.

reflexivity.

Qed.

Lemma xor_two_bits_oracle_correct :

  forall x,

  oracle_xor_two_bits x = xor_two_bits x.

Proof.

reflexivity.

Qed.

Theorem parity_oracle_correct :

  forall x,

  oracle_parity x = parity x.

Proof.

reflexivity.

Qed.

Theorem example_balanced_satisfies_promise :

  forall n,

  DJPromise n oracle_example_balanced.

Proof.
Admitted.