(*************************************************************)
(* Enumeration.v                                             *)
(*                                                           *)
(* Exhaustive enumeration of finite bitstrings.              *)
(* These definitions allow finite verification of Boolean    *)
(* functions and quantum oracle properties.                  *)
(*************************************************************)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

Require Import DJ.Foundations.BitStrings.

(*************************************************************)
(* Helper Functions                                          *)
(*************************************************************)
Definition prepend_bit
    (b : Bit)
    (l : list BitString)
    : list BitString :=

map (fun x => b :: x) l. (* This is a helper function that takes a bit and a list of bitstrings, and returns a new list of bitstrings where the given bit is prepended to each bitstring in the original list.*)

(*************************************************************)
(* Enumeration                                               *)
(*************************************************************)
Fixpoint enumerate_bitstrings
    (n : nat)
    : list BitString :=

match n with

| O =>
    [[]]

| S k =>

    prepend_bit false (enumerate_bitstrings k)

    ++

    prepend_bit true (enumerate_bitstrings k)

end. (* This function generates all possible bitstrings of length n. It does this recursively by generating all bitstrings of length k (where k = n - 1), and then prepending both false and true to each of those bitstrings to create the full set of bitstrings of length n.*)

(*************************************************************)
(* Utilities                                                 *)
(*************************************************************)
Definition number_of_inputs
           (n : nat)
           : nat :=
  Nat.pow 2 n. (*This definition calculates the number of possible input combinations for a given number of bits.*)

Definition valid_input
    (n : nat)
    (x : BitString)
    : Prop :=

In x (enumerate_bitstrings n). (* This definition checks if a given bitstring is a valid input for a given number of bits.*)

Definition enumerate_outputs
           {A}
           (f : BitString -> A)
           (n : nat)
           : list A :=
  map f (enumerate_bitstrings n).

(*************************************************************)
(* Examples                                                  *)
(*************************************************************)
Theorem enumerate_zero :

enumerate_bitstrings 0 = [[]].
Proof.
reflexivity.
Qed. (* This theorem states that there is only one bitstring of length 0, which is the empty list.*)

Theorem enumerate_one :

enumerate_bitstrings 1 =

[[false];
 [true]].
Proof.
reflexivity.
Qed. (* This theorem states that there are two bitstrings of length 1: one containing false and one containing true.*)

Theorem enumerate_two :

enumerate_bitstrings 2 =

[
[false;false];
[false;true];
[true;false];
[true;true]
].
Proof.
reflexivity.
Qed. (* This theorem states that there are four bitstrings of length 2: [false;false], [false;true], [true;false], and [true;true]. *)

(*************************************************************)
(* General Lemmas                                            *)
(*************************************************************)
Lemma enumerate_length :

forall n,

length (enumerate_bitstrings n)

=

Nat.pow 2 n.
Proof.
Admitted.

Lemma valid_input_complete :

forall n x,

valid_input n x ->

length x = n.
Proof.
Admitted.

Lemma enumerate_nonempty :
  forall n,
    enumerate_bitstrings n <> [].
Proof.
Admitted.

