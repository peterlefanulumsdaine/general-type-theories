Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import RawSyntax.All.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Typed.TypedRule.

(** In this file: definition of well-typedness of a type-theory. *)

Section WellTypedTypeTheory.

  Context {σ : shape_system}.

  Local Definition is_well_typed (T : raw_type_theory σ) : Type.
  Proof.
    simple refine (forall R : T, TypedRule.is_well_typed _ (tt_rule R)).
    refine (FlatTypeTheory.fmap _ _).
    - apply RawTypeTheory.initial_segment_signature_to_rule_signature.
    - apply RawTypeTheory.flatten.
  Defined.

End WellTypedTypeTheory.

Record type_theory {σ : shape_system} : Type
  := { tt_raw_type_theory :> raw_type_theory σ
     ; tt_well_typed : is_well_typed tt_raw_type_theory }.
