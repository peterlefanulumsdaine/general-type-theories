From HoTT Require Import HoTT.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.PresentedRawRule.
Require Import Presented.PresentedRawTypeTheory.
Require Import Presented.TypedRule.

(** In this file: definition of well-typedness of a type-theory. *)

Section WellTypedTypeTheory.

  Context {σ : scope_system}.

  Local Definition is_well_typed (T : presented_raw_type_theory σ) : Type.
  Proof.
    simple refine (forall R : T, TypedRule.is_well_typed _ (tt_rule R)).
    refine (RawTypeTheory.fmap _ _).
    - apply PresentedRawTypeTheory.initial_segment_signature_to_rule_signature.
    - apply PresentedRawTypeTheory.flatten.
  Defined.

End WellTypedTypeTheory.

Record type_theory (σ : scope_system) : Type
  := { tt_presented_raw_type_theory :> presented_raw_type_theory σ
     ; tt_well_typed : is_well_typed tt_presented_raw_type_theory }.
