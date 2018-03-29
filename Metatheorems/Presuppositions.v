Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.

Section Presuppositions_Derivable.

  Context {σ : shape_system}.
  
  Theorem presuppositions_derivable {T : Type_Theory σ}
      {j : judgement_total (Signature_of_Type_Theory T)}
      (dj : Derivation_from_Type_Theory T [<>] j)
      {p : presupposition (pr2 j) }
    : Derivation_from_Type_Theory T [<>] (presupposition (pr2 j) p).
    (* TODO: at least make access function between [judgment] and [judgement_total]; perhaps make it a coercion? *)
  Proof.
  Admitted.

End Presuppositions_Derivable.
  