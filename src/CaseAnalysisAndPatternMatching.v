(* 3 - Case Analysis and Pattern-matching *)


(* 3.1 Non-dependent Case Analysis *)

(* An elimination rule for the type A is some way to use an object a : A in
   order to define an object in some type B. A natural elimination for an
   inductive type is case analysis.

   For instance, any value of type nat is built using either O or S. Thus, a
   systematic way of building a value of type B from any value of type nat is
   to associate to O a constant t0 : B, and to every term of the form 'S p'
   a term ts : B. The following construction has type B:

     match n return B with
     | O => t0
     | S p => ts
     end

    In most of the case, Coq is able to infer the type B of the object
    defined, so the 'return B' part may be omitted. The computing rules
    associated with construct are the expected ones:

      match O return B with O => t0 | S p => ts end ==> to

      match S q return B with O => t0 | S p => ts end ==> ts{q/p} *)


(* 3.2 Dependent Case Analysis *)

(* For a pattern matching construct of the form 'match n with ... end', a
   more general typing rule is obtained considering that the type of the
   whole expression may also depend on n. For instance, consider some
   function Q : nat -> Set, and n : nat. In order to build a term of type Q n,
   we can associate to the constructor O some term tO : Q O and to the pattern
   'S p' some term tS : Q (S p). Note that the terms tO and tS do not have
   the same type. The syntax of the dependent case analysis and its
   associated typing rule are as follows:

     Q : nat -> Set    tO : Q O    p : nat |- tp : Q (S p)    n : nat
    ------------------------------------------------------------------
     match n as nO return Q nO with | O => tO | S p => tS end : Q n

   The former, non-dependent version of case analysis can be obtained from
   this latter rule by taking Q as a constant function on n. *)

(* Strong specification of the predecessor function *)
Definition pred_spec (n : nat) :=
  { m : nat | n = O /\ m = O \/ n = S m }.

Definition predecessor : forall n : nat, pred_spec n.
  intro n; case n.
  unfold pred_spec; exists O; auto.
  unfold pred_spec; intro n'; exists n'; auto.
Defined.

Print predecessor.
Extraction predecessor.

(* Exercise 3.1 *)
Theorem nat_expand : forall n : nat,
  n = match n with
      | O => O
      | S p => S p
      end.
Proof.
  intro n; induction n; reflexivity.
Qed.

(* The Empty type *)

(* The rule of (non-dependent) case analysis for the type False is (for
   s in Prop, Set or Type):

     Q : s    p : False
    --------------------
     match p return Q with end : Q
*)

Theorem fromFalse : False -> 0 = 1.
Proof. intros; contradiction. Qed.

Print not.

Fact Nosense : O <> O -> 2 = 3.
Proof. intro H; case H; reflexivity. Qed.
