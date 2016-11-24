Require Import Auxiliary
               RawSyntax
               Vectors.Fin.





Definition deBruijn : ProtoCxtSystem.
Proof.
  simple refine (Build_ProtoCxtSystem _ _ _ _ _ _).
  - exact nat.
  - exact Fin.t. (* should be fin *)
  - admit. (* should be + *)
  - admit.
  - admit. (* should be +1 *)
  - admit.
Admitted.

Definition natVars : ProtoCxtSystem.
Proof.
  simple refine (Build_ProtoCxtSystem _ _ _ _ _ _).
  - admit. (* finite subsets of nat *)
  - admit. (* should be El *)
  - admit. (* should be some implementation of disjoint union *)
  - admit.
  - admit. (* should be some choice of fresh var *)
  - admit.
Admitted.

(* TODO: Should also generalise to any constructively infinite type. *)