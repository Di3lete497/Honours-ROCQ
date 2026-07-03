Require Import List.
Require Import Bool.

Import ListNotations.

Definition Bit := bool.

Definition BitString := list Bit.

Definition bit_length (b : BitString) : nat :=
    length b.

Definition xor (a b : Bit) : Bit :=
    xorb a b.

Definition bit_not (b : Bit) : Bit :=
    negb b.


Fixpoint count_ones (b : BitString) : nat :=

match b with

| [] => 0

| true :: xs =>
    S (count_ones xs)

| false :: xs =>
    count_ones xs

end.


Definition count_zeros (b : BitString) : nat :=

length b - count_ones b.



Fixpoint parity (b : BitString) : Bit :=

match b with

| [] => false

| x :: xs =>
    xor x (parity xs)

end.

Definition first_bit (b : BitString) : Bit :=

match b with

| [] => false

| x :: _ => x

end.
