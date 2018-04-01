Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Raw.FlatTypeTheoryMap.
Require Import Typed.TypedRule.

(** In this file: definition of well-typedness of a type-theory. *)

Section WellTypedTypeTheory.

  Context {σ : shape_system}.

  Definition is_well_typed_type_theory (T : raw_type_theory σ) : Type.
  Proof.
    simple refine (forall R : T, TypedRule.is_well_typed_rule _ (tt_rule R)).
    refine (FlatTypeTheory.fmap _ _).
    - apply RawTypeTheory.subtheory_signature.
    - apply RawTypeTheory.flatten.
  Defined.

End WellTypedTypeTheory.

Record type_theory {σ : shape_system} : Type
  := { raw_type_theory_of_well_typed :> raw_type_theory σ
       ; is_well_typed : is_well_typed_type_theory
                           raw_type_theory_of_well_typed }.
