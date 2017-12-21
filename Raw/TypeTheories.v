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

Section Derivable_Rules.

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  (* TODO: abstract in terms of a derivation of a closure condition from a family thereof. *)
  Definition Derivation_Raw_Rule_from_Raw_TT
      (R : Raw_Rule Σ) (T : Raw_Type_Theory Σ)
    : Type.
  Proof.
    set (Σ' := Metavariable_Extension Σ (RR_metas _ R)).
    assert (f : Signature_Map Σ Σ').
      apply inl_Family. (* TODO: make this a lemma about signature maps,
                         so it’s more findable using “SearchAbout” etc *)
    refine (Derivation _ (RR_concln _ R)).
    refine (_ + _).
    - apply CCs_from_Raw_TT.
      exact (Fmap_Raw_TT f T).
    - refine (Fmap _ (RR_prem _ R)).
      apply singleton_cc.
  Defined.

End Derivable_Rules.

(* TODO:
  - a map of raw type theories, over a map of signatures, is a function giving a derivation of the translation of each raw rule.
  - this should extend to a map of “closure systems” (to be defined!), and hence to a map on derivations.
*)