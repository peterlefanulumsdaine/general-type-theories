Require Import Auxiliary.Family.

(* A closure condition on [X] says that whenever all elements of
   [cc_premises] is in a set then so is [cc_conclusion]. *)
Record closure_condition (X : Type)
:=
  { cc_premises : Family X
  ; cc_conclusion : X
  }.

Arguments cc_premises [_] _.
Arguments cc_conclusion [_] _.

Definition singleton_cc {X} (x:X) : closure_condition X
:=
  {| cc_premises := Empty_family _
  ; cc_conclusion := x
|}.

Definition Fmap_cc {X X'} (f : X -> X')
  : closure_condition X -> closure_condition X'.
Proof.
  intros [c_prem c_conc].
  apply Build_closure_condition.
  - exact (Fmap_Family f c_prem).
  - exact (f c_conc).
Defined.

(* (Closed) derivations under a family of closure conditions. *)
Inductive Derivation {X} (C : Family (closure_condition X))
  : X -> Type
:= deduce (i : C)
    : (forall p : cc_premises (C i), Derivation C (cc_premises _ p))
      -> Derivation C (cc_conclusion (C i)).

(* Derivations from a given family of “premises”, using a family of closure conditions. *)
Definition Derivation_from_premises {X} (C : Family (closure_condition X))
  (P : Family X) : X -> Type
:= Derivation (C + (Fmap_Family singleton_cc P)).

(* TODO: move*)
Delimit Scope fam_scope with fam.

Definition Derivation_glue {X} (C : Family (closure_condition X))
    {P} {x} (d : Derivation_from_premises C P x)
    (dP : forall i:P, Derivation C (P i))
  : Derivation C x.
Proof.
  induction d as [[c | p] d' IH_d'].
  - refine (deduce _ c _). intros p.
    apply IH_d'.
  - apply dP.
Defined.

Definition Derivation_of_CC {X} (C : Family (closure_condition X))
  (c : closure_condition X) : Type
:= Derivation_from_premises C (cc_premises c) (cc_conclusion c).

Definition closure_system_map {X} (C C' : Family (closure_condition X)) : Type
:= forall c : C, Derivation_of_CC C' (C c).

Fixpoint Fmap_Derivation {X}
  {C C' : Family (closure_condition X)} (f : closure_system_map C C')
  {x:X} (d : Derivation C x) : Derivation C' x.
Proof.
  destruct d as [c d'].
  refine (Derivation_glue _ _ _).
  - apply f.
  - intros i. apply (Fmap_Derivation _ _ _ f), d'.
Defined.
