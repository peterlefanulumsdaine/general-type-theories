Require Import Auxiliary.Family.

(* A closure condition on [X] says that whenever all elements of
   [cc_premises] is in a set then so ic [cc_conclusion]. *)
Record closure_condition (X : Type)
:=
  { cc_premises : Family X
  ; cc_conclusion : X
  }.

Arguments cc_premises [_] _.
Arguments cc_conclusion [_] _.

(* A derivation with respect to a family of closure conditions. *)
Inductive Derivation {X} (C : Family (closure_condition X))
  : X -> Type
:= deduce (i : C)
    : (forall p : cc_premises (C i), Derivation C (cc_premises _ p))
      -> Derivation C (cc_conclusion (C i)).

