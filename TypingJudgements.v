Require Import HoTT.
Require Import ShapeSystems.
Require Import DeductiveClosure.
Require Import Family.
Require Import RawSyntax.
Require Import RawTypeTheories.
Require Import StructuralRules.
Require Import SignatureMaps.

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

Section Derivability_from_TT_Spec.

  Context {σ : Shape_System}.

  Definition Raw_TT_of_TT_Spec (T : Type_Theory_Spec σ)
    : Raw_Type_Theory (Signature_of_TT_Spec T).
  Proof.
    refine (_ + _).
    (* First: the explicitly-given logical rules *)
    - exists (TTS_Rule T).
      intros r.
      refine (Raw_Rule_of_Rule_Spec _ _).
      + (* translate rule_specs up to the full signature *)
        refine (Fmap_Rule_Spec _ (TTS_rule_spec r)).
        apply TT_Spec_signature_inclusion_of_rule.
      + (* pick their symbol in the full signature, if applicable *)
        intros r_obj.
        exists (r; r_obj).
        split; apply idpath.
    (* Second: associated congruence rules for the object-judgement logical rules. *)
    - exists { r : TTS_Rule T & is_obj_HJF (TTS_hjf_of_rule r) }.
      intros [r Hr].
      refine (Raw_Rule_of_Rule_Spec _ _).
      + simple refine
        (associated_congruence_rule_spec
           (Fmap_Rule_Spec _ (TTS_rule_spec r)) _ _ _ _).
        * apply TT_Spec_signature_inclusion_of_rule.
        * exact Hr.
        * exact (r;Hr). (* head symbol of original rule *)
        * apply idpath.
        * apply idpath.
      + intros []. (* no head symbol, since congs are equality rules *)
  Defined.

  Definition Derivation_from_TT_Spec (T : Type_Theory_Spec σ)
    : Judgt_Instance (Signature_of_TT_Spec T) -> Type
  := Derivation_from_Raw_TT (Raw_TT_of_TT_Spec T).

End Derivability_from_TT_Spec.
