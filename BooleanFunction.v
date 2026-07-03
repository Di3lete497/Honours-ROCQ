(*************************************************************)
(* Boolean Functions Used by Quantum Oracles                 *)
(*************************************************************)

From Coq Require Import List Bool Arith.
Import ListNotations.

Require Import DJ.BitStrings.

(*************************************************************)
(* Types                                                     *)
(*************************************************************)

Definition Bit := bool.

Definition Oracle := BitString -> Bit.

Definition evaluate
           (f : Oracle)
           (x : BitString)
           : Bit :=
  f x.

(* FOR Marked-State Oracles *)

Fixpoint bitstring_eqb
         (x y : BitString)
         : bool :=

  match x, y with
  | [], [] => true
  | b1::x', b2::y' =>
      andb (Bool.eqb b1 b2)
           (bitstring_eqb x' y')
  | _, _ => false
  end.


Definition first_bit
           (x : BitString)
           : bool :=

  match x with
  | [] => false
  | b::_ => b
  end.


Fixpoint parity
         (x : BitString)
         : bool :=

  match x with
  | [] => false
  | b::xs =>
      xorb b (parity xs)
  end.

Definition xor_two_bits
           (x : BitString)
           : bool :=

  match x with
  | b1::b2::_ =>
      xorb b1 b2
  | _ => false
  end.

Definition affine
           (x : BitString)
           : bool :=

  xorb (parity x) true.

(*For Invalid Oracles*)

Fixpoint count_true_bits
         (x : BitString)
         : nat :=

  match x with
  | [] => 0
  | true::xs =>
      S (count_true_bits xs)
  | false::xs =>
      count_true_bits xs
  end.

Definition majority
           (x : BitString)
           : bool :=

  Nat.leb
    (length x / 2 + 1)
    (count_true_bits x).

Fixpoint all_ones
         (n : nat)
         : BitString :=

  match n with
  | 0 => []
  | S k =>
      true :: all_ones k
  end. (* FOR MARKED STATE ORACLES *)

Fixpoint all_zeros
         (n : nat)
         : BitString :=

  match n with
  | 0 => []
  | S k =>
      false :: all_zeros k
  end.

Definition alternating
           (x : BitString)
           : bool :=

  negb (first_bit x).