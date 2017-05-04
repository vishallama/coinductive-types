(* 2 - Introducing Inductive Types *)


Module Nat.

(* Inductive types are types closed with respect to their introduction rules.
   These rules explain the most basic or canonical ways of constructing an
   element of the type. In this sense, they characterize the recursive type.
   Different rules must be considered as introducing different objects. The
   most well-known example of a recursive type is that of the natural
   numbers. *)
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(* The definition of a recursive type has two main parts.

   1. We establish the characterization of the kind of recursive type (a set,
      in this case.)

   2. We present the introduction rules (O and S), also called its
      constructors, that define the type. That is if n : nat, then n must
      have been introduced either by the rule O or by an application of the
      rule S to a previously constructed natural number object. In this sense,
      nat is closed, whereas Set is an open type, since we do not know
      a priori all the possible ways of introducing an object of type Set. *)
End Nat.


(* 2.1 Lists *)
Require Import List.
Print list.

(* In the definition of list, A is a general parameter, global to both
   constructors. This kind of definition allows us to build a whole family of
   inductive types, indexed over the sort Type. *)
Check list.
Check (nil (A := nat)).
Check (nil (A := nat -> nat)).
Check (fun A : Set => (cons (A := A))).
Check (cons 1 (cons 2 (cons 3 nil))).
