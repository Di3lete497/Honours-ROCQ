Require Import List.
Require Import Bool.

Import ListNotations.

Require Import DJ.BitStrings.

Definition prefix_bit
    (b : Bit)
    (l : list BitString)
    : list BitString :=

map (fun x => b :: x) l. (* This is a helper function that takes a bit and a list of bitstrings, and returns a new list of bitstrings where the given bit is prepended to each bitstring in the original list.*)

Fixpoint all_bitstrings
    (n : nat)
    : list BitString :=

match n with

| O =>
    [[]]

| S k =>

    prefix_bit false (all_bitstrings k)

    ++

    prefix_bit true (all_bitstrings k)

end. (* This function generates all possible bitstrings of length n. It does this recursively by generating all bitstrings of length k (where k = n - 1), and then prepending both false and true to each of those bitstrings to create the full set of bitstrings of length n.*)

Definition number_of_inputs
    (n : nat)
    : nat :=

length (all_bitstrings n). (*This definition calculates the number of possible input combinations for a given number of bits.*)

Definition valid_input
    (n : nat)
    (x : BitString)
    : Prop :=

In x (all_bitstrings n). (* This definition checks if a given bitstring is a valid input for a given number of bits.*)

Theorem enumerate_zero :

all_bitstrings 0 = [[]].
Proof.
reflexivity.
Qed. (* This theorem states that there is only one bitstring of length 0, which is the empty list.*)

Theorem enumerate_one :

all_bitstrings 1 =

[[false];
 [true]].
Proof.
reflexivity.
Qed. (* This theorem states that there are two bitstrings of length 1: one containing false and one containing true.*)

Theorem enumerate_two :

all_bitstrings 2 =

[
[false;false];
[false;true];
[true;false];
[true;true]
].
Proof.
reflexivity.
Qed. (* This theorem states that there are four bitstrings of length 2: [false;false], [false;true], [true;false], and [true;true]. *)