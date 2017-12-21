Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystems.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.DeductiveClosure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMaps.
Require Import Raw.StructuralRules.

Section Derivability_from_Raw_TT.

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  Definition CCs_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Family (closure_condition (Judgt_Instance Σ))
  := Structural_CCs Σ
     + Family.Bind T CCs_of_RR.

  Definition Derivation_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Judgt_Instance Σ -> Type
  := Derivation (CCs_from_Raw_TT T).
  
End Derivability_from_Raw_TT.

