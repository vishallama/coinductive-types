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


(* 2.5 Relations as inductive types *)

(* In the definiton of le, n is a general parameter, while the second
   argument of le is an index, which is instantiated differently in the
   introduction rules. Such types parameterized by regular values are called
   dependent types. *)
Print le.

Theorem zero_leq_three : O <= 3.
Proof.
  (* Use a direct proof *)
  apply (le_S O 2 (le_S O 1 (le_S O O (le_n O)))).
Qed.

Theorem zero_leq_three' : O <= 3.
Proof.
  (* Automated proof *)
  repeat constructor.
Qed.

Print lt.

Lemma zero_lt_three : O < 3.
Proof. unfold lt; repeat constructor. Qed.


(* 2.6 The propositional equality type *)

(* In Coq, the propositional equality between two inhabitants a and b of the
   same type A, denoted a = b, is introduced as a family of recursive
   predicates, parameterized by both a and its type A. This family of types
   has only one introduction rule, which corresponds to reflexivity. The
   syntax 'a = b' is an abbreviation for 'eq a b', and the parameter A is
   implicit. *)
Print eq.

(* The type system of Coq allows us to consider equality between various
   kinds of terms: elements of a set, proofs, propositions, types, and so
   on. *)
Lemma eq_3_3 : 2 + 1 = 3.
Proof. reflexivity. Qed.

Lemma eq_proof_proof : eq_refl (2*6) = eq_refl (3*4).
Proof. reflexivity. Qed.

Lemma eq_lt_le : (2 < 4) = (3 <= 4).
Proof. reflexivity. Qed.

Lemma eq_nat_nat : nat = nat.
Proof. reflexivity. Qed.

Lemma eq_Set_Set : Set = Set.
Proof. reflexivity. Qed.


(* 2.7 Logical connectives *)

(* The type sumbool is a disjunction but with computational contents. This
   type can be used in Coq programs as a sort of boolean type to check whether
   it is A or B that is true. The values 'left p' and 'right q' replace the
   boolean values true and false, respectively. The advantage of this type
   over bool is that it makes available the proofs p of A or q of B, which
   could be necessary to construct a verification proof about the program. *)
Print sumbool.

Require Import Compare_dec.
Check le_lt_dec.

Definition max (n p : nat) :=
  match le_lt_dec n p with
  | left _ => p
  | right _ => n
  end.

(* In the following proof, the case analysis on the term 'le_lt_dec n p'
   gives us access to proofs of n <= p in the first case, p < n in the
   other *)
Theorem le_max : forall n p, n <= p -> max n p = p.
Proof.
  intros n p; unfold max; case (le_lt_dec n p); simpl.
  - (* n <= p *) intros; reflexivity.
  - (* p < n *) intros; absurd (p < p); eauto with arith.
Qed.

(* Once the program is verified, the proofs are erased by the extraction
   procedure *)
Extraction max.
