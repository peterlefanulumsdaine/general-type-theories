
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.
Require Import Raw.FlatTypeTheoryMap.

Section WellTypedFlatRule.

  Context {σ : shape_system}.

  Local Definition is_well_typed {Σ : signature σ}
    (T : flat_type_theory Σ) (r : flat_rule Σ) : Type.
  Proof.
    refine (_ * _).
    - exact (forall p : flat_rule_premises _ r,
        FlatTypeTheory.presupposition_derivation
          (FlatTypeTheory.fmap include_symbol T)
          (boundary_of_judgement (projT2 (flat_rule_premises _ _ p)))
          (flat_rule_premises _ r)).
    - exact (FlatTypeTheory.presupposition_derivation
          (FlatTypeTheory.fmap include_symbol T)
          (boundary_of_judgement (projT2 (flat_rule_conclusion _ r)))
          (flat_rule_premises _ r)).
  Defined.
(* TODO: make signature implicit in args of [flat_rule] fields. 
   TODO: rename [flat_rule_premises] to [flat_rule_premise] *)

End WellTypedFlatRule.
