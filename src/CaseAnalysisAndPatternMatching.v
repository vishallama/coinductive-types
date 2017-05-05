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
