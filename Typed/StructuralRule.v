Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.StructuralRule.
Require Import Typed.Closure.
Require Import Typed.Derivation.
Require Import Typed.FlatRule.

(** Main goal for this file: show all the structural rules are well-typed.

For the ones stated as flat rules, this means showing they’re well-typed as such: i.e. showing that whenever their premises hold, then all the presuppositions of both their premises and conclusion hold. *)

Section Welltypedness.

  Context {σ : shape_system}.

  Local Lemma well_typed {Σ : signature σ}
    : Closure.well_typed presupposition (StructuralRule.Structural_CCs Σ).
  Admitted.

End Welltypedness.