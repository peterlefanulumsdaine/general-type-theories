Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.
Require Import Typed.TypedRule.

(** In this file: definition of well-typedness of a type-theory. *)

Section Welltypedness.

  Context {σ : shape_system}.

  Definition is_well_typed_type_theory (T : raw_type_theory σ) : Type.
  Proof.
    refine (forall R : T, _).
    refine (is_well_typed_rule _ (tt_rule R)).
    refine (fmap_flat_type_theory _ _).
    Focus 2. { refine (@TypeTheory.flatten _ _).
      exact (TypeTheory.subtheory T R). }
    Unfocus.
    apply TypeTheory.subtheory_signature.
  Defined.

End Welltypedness.

Section TypeTheory.

  Context {σ : shape_system}.

  Record type_theory : Type
  := { raw_type_theory_of_well_typed :> raw_type_theory σ
     ; is_well_typed : is_well_typed_type_theory
                         raw_type_theory_of_well_typed }.

End TypeTheory.
