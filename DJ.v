(*************************************************************)
(* Abstract Deutsch-Jozsa Algorithm                          *)
(*************************************************************)

From Coq Require Import Bool List.

Import ListNotations.

Require Import DJ.BitStrings.
Require Import DJ.BooleanFunctions.
Require Import DJ.Promise.
Require Import DJ.Oracles.

(*************************************************************)
(* Output Type                                               *)
(*************************************************************)

Definition Output := BitString.

(*************************************************************)
(* Initial State                                             *)
(*************************************************************)

Fixpoint zero_state
         (n : nat)
         : BitString :=

match n with

| O => []

| S k => false :: zero_state k

end.

(*************************************************************)
(* Abstract Quantum Operations                               *)
(*************************************************************)

Parameter Hadamard :

BitString -> BitString.

Parameter ApplyOracle :

Oracle -> BitString -> BitString.

Parameter Measure :

BitString -> Output.
(*Currenly Abstract Functions but later we will prove properties about them*)

(*************************************************************)
(* Deutsch-Jozsa Algorithm                                   *)
(*************************************************************)

Definition DJ
           (f : Oracle)
           (n : nat)
           : Output :=

Measure
(
Hadamard
(
ApplyOracle
f
(
Hadamard
(
zero_state n
)
)
)
).

(*************************************************************)
(* Expected Behaviour                                        *)
(*************************************************************)

Definition DJAccepts
           (f : Oracle)
           (n : nat)
           : Prop :=

OutputZero (DJ f n).

Definition DJRejects
           (f : Oracle)
           (n : nat)
           : Prop :=

OutputNonZero (DJ f n).

(*************************************************************)
(* Correctness Specification                                 *)
(*************************************************************)

Definition DJCorrect
           (f : Oracle)
           (n : nat)
           : Prop :=

(Constant f -> DJAccepts f n)
/\
(Balanced f -> DJRejects f n).

(*************************************************************)
(* Promise-aware Correctness                                 *)
(*************************************************************)

Definition DJVerified
           (f : Oracle)
           (n : nat)
           : Prop :=

PromiseSatisfied f
/\ DJCorrect f n.