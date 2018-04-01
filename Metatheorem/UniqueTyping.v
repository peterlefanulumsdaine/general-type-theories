

Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.
Require Import Typed.TypeTheory.

(* Main goal of this file: theorem stating unique typing, for any (fully typed) type theory. *)

Theorem unique_typing {σ : shape_system} (T : raw_type_theory σ)
    (Σ := TypeTheory.signature T)
    (Γ : raw_context Σ) (a : raw_term Σ Γ) (A A' : raw_type Σ Γ)
    (d : Derivation_from_Type_Theory T [<>] [Tm! Γ |- a ; A !])
    (d' : Derivation_from_Type_Theory T [<>] [Tm! Γ |- a ; A' !])
  : Derivation_from_Type_Theory T [<>] [TyEq! Γ |- A ≡ A' !].
Abort.

(* Sketch proof: ????

Presumably: will need to generalised to derivations with hypotheses — specifcally, to derivations over an arbitrary _algebraic extension_ of a type theory. *)