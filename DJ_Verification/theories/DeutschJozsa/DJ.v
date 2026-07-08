(*************************************************************)
(* Abstract Deutsch-Jozsa Algorithm                          *)
(*************************************************************)

From Coq Require Import Bool List.

Import ListNotations.

Require Import DJ.Foundations.BitStrings.
Require Import DJ.Oracles.BooleanFunctions.
Require Import DJ.Oracles.Oracles.

Require Import DJ.Verification.Balanced.
Require Import DJ.Oracles.Promise.

(*************************************************************)
(* Output Type                                               *)
(*************************************************************)

Definition Output := BitString.

(*************************************************************)
(* Initial State                                             *)
(*************************************************************)

Definition zero_state := all_zeros.

Definition ZeroOutput
           (n : nat)
           : Output :=

zero_state n.

(*
These operators are intentionally abstract.

Later they will be instantiated using
verified quantum semantics and
proved to satisfy the Deutsch–Jozsa specification.
*)

(*************************************************************)
(* Abstract Quantum Operations                               *)
(*************************************************************)

Parameter ApplyHadamard :

BitString -> BitString.

Parameter ApplyOracle :

Oracle -> BitString -> BitString.

Parameter Measure :

BitString -> Output.
(*Currenly Abstract Functions but later we will prove properties about them*)

(*************************************************************)
(* Deutsch-Jozsa Algorithm                                   *)
(*************************************************************)

Definition DeutschJozsa
           (f : Oracle)
           (n : nat)
           : Output :=

  Measure
    (ApplyHadamard
      (ApplyOracle f
        (ApplyHadamard (zero_state n)))).

Notation DJ := DeutschJozsa.

(*
DeutschJozsa is intentionally abstract.

Later chapters instantiate

ApplyHadamard

ApplyOracle

Measure

using verified quantum semantics.
*)

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

Definition DJAlgorithmCorrect
           (n : nat)
           (f : Oracle)
           : Prop :=

(Constant n f ->
 DJAccepts f n)

/\

(Balanced n f ->
 DJRejects f n).

(*************************************************************)
(* Promise-aware Correctness                                 *)
(*************************************************************)

Definition DJVerified
           (n : nat)
           (f : Oracle)
           : Prop :=

PromiseHolds n f

/\

DJAlgorithmCorrect n f.


Definition DJResult
           (f : Oracle)
           (n : nat)
           : Output :=

DJ f n.

Definition Executes
           (f : Oracle)
           (n : nat)
           : Prop :=

exists result,

result = DJ f n.

(*************************************************************)
(* Lemma                                                     *)
(*************************************************************)
Lemma DJ_returns_output :

forall f n,

exists out,

DJ f n = out.

Proof.

intros.

exists (DJ f n).

reflexivity.

Qed.

Lemma executes_exists :

forall f n,

Executes f n.

Proof.

intros.

unfold Executes.

exists (DJ f n).

reflexivity.

Qed.

Lemma DJResult_unfold :

forall f n,

DJResult f n = DJ f n.

Proof.

reflexivity.

Qed.

Lemma DJVerified_unfold :

forall n f,

DJVerified n f

<->

PromiseHolds n f

/\

DJAlgorithmCorrect n f.

Proof.

firstorder.

Qed.

Lemma DJAlgorithmCorrect_split :

forall n f,

DJAlgorithmCorrect n f

->

(Constant n f -> DJAccepts f n)

/\

(Balanced n f -> DJRejects f n).

Proof.

firstorder.

Qed.