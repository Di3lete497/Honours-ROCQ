From Coq Require Import List Bool Arith Lia ZArith.

Import ListNotations.

Open Scope Z_scope.

Require Import BitStrings.
Require Import Enumeration.

(*************************************************************)
(* Boolean Oracles                                           *)
(*************************************************************)

Definition Oracle (n : nat) := BitString n -> bool.

(*************************************************************)
(* Oracle Evaluation                                         *)
(*************************************************************)
Definition evaluate_oracle
           {n}
           (f : Oracle n)
           (x : BitString n)
           : bool :=
  f x.

Definition oracle_outputs
           {n}
           (f : Oracle n)
           : list bool :=
  map f (enumerate_bitstrings n).

(*************************************************************)
(* Counting                                                  *)
(*************************************************************)
Fixpoint count_true
         (l : list bool)
         : nat :=
  match l with
  | [] => 0
  | true :: xs =>
      S (count_true xs)
  | false :: xs =>
      count_true xs
  end.

Fixpoint count_false
         (l : list bool)
         : nat :=
  match l with
  | [] => 0
  | true :: xs =>
      count_false xs
  | false :: xs =>
      S (count_false xs)
  end.

Definition count_true_outputs
           {n}
           (f : Oracle n)
           : nat :=
  count_true (oracle_outputs f).
  
Definition count_false_outputs
           {n}
           (f : Oracle n)
           : nat :=
  length (oracle_outputs f)
  -
  count_true_outputs f.

Definition count_outputs
           {n}
           (f : Oracle n)
           : nat * nat :=
(
count_true_outputs f,
count_false_outputs f
).

(*************************************************************)
(* Total number of outputs                                   *)
(*************************************************************)
Definition total_outputs
           (n : nat)
           : nat :=
  Nat.pow 2 n.


Definition output_bias
           {n}
           (f : Oracle n)
           : nat * nat :=
(
count_true_outputs f,
total_outputs n
).

(*************************************************************)
(* Distance from Balance                                     *)
(*************************************************************)

Definition balance_distance
           {n}
           (f : Oracle n)
           : nat :=

let expected := total_outputs n / 2 in

Nat.sub
  (Nat.max (count_true_outputs f) expected)
  (Nat.min (count_true_outputs f) expected).


Definition total_fraction
           {n}
           (f : Oracle n)
           : nat * nat :=
(
count_true_outputs f,
count_true_outputs f +
count_false_outputs f
).

Definition all_true
           (l : list bool)
           : bool :=
  forallb (fun b => b) l.


Definition all_false
           (l : list bool)
           : bool :=
  forallb negb l.

(* EXAMPLES FOR DEBUGGING*)
Compute total_outputs 3.
Compute total_outputs 4.
Compute total_outputs 5.

