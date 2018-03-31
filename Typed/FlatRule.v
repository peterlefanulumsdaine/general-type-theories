
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.FlatRule.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.

Section Welltypedness.

  Context {σ : shape_system}.

  Local Definition is_well_typed {Σ : signature σ}
    (T : flat_type_theory Σ) (r : flat_rule Σ) : Type.
  Proof.
    refine (_ * _).
    - exact (forall p : flat_rule_premises _ r,
        Derivation_Judgt_Bdry_Instance
          (fmap_flat_type_theory include_symbol T)
          (boundary_of_judgement (projT2 (flat_rule_premises _ _ p)))
          (flat_rule_premises _ r)).
    - exact (Derivation_Judgt_Bdry_Instance
          (fmap_flat_type_theory include_symbol T)
          (boundary_of_judgement (projT2 (flat_rule_conclusion _ r)))
          (flat_rule_premises _ r)).
  Defined.
(* TODO: make signature implicit in args of [flat_rule] fields. 
   TODO: rename [flat_rule_premises] to [flat_rule_premise] *)

End Welltypedness.