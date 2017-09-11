Require Import HoTT.
Require Import ShapeSystems.
Require Import DeductiveClosure.
Require Import Family.
Require Import RawSyntax.
Require Import RawTypeTheories.
Require Import StandardRawRules.
Require Import SignatureMaps.

Section Derivability_from_Raw_TT.
(* TODO: this section could be moved into RawTypeTheories.v, if only the context cc’s were also upstreamed so this didn’t depend on StandardRawRules.v.  Consider this? *)

  Context {σ : Shape_System}
          {Σ : Signature σ}.

  Definition CCs_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Family (closure_condition (Judgt_Instance Σ)).
  Proof.
    refine (Family.Sum (context_ccs Σ) _).
    exact (Family.Bind T CCs_of_RR).
  Defined.

  Definition Derivation_from_Raw_TT (T : Raw_Type_Theory Σ)
    : Judgt_Instance Σ -> Type
  := Derivation (CCs_from_Raw_TT T).
  
End Derivability_from_Raw_TT.

Section Derivability_from_TT_Spec.

  Context {σ : Shape_System}.

  (* TODO: upstream to with TT_Spec *)
  Definition Signature_of_TT_Spec (T : Type_Theory_Spec σ)
    : Signature σ.
  Proof.
    (* symbols are given by the object-judgement rules of T *)
    exists {r : TTS_Rule T & is_obj_HJF (TTS_hjf_of_rule r)}.
    intros r_H. set (r := pr1 r_H).
    split.
    - exact (class_of_HJF (TTS_hjf_of_rule r)).
    - exact (TTS_arity_of_rule r
            + simple_arity (TTS_concl_shape_of_rule r)).
  Defined.
    (* NOTE: it is tempting to case-analyse here and say 
      “when r is an object rule, use [(class_of_HJF hjf, TTS_arity_of_rule r)];
       in case r is an equality rule, use reductio ad absurdum with Hr.” 
     But we get stronger reduction behaviour by just taking [(class_of_HJF hjf, TTS_arity_of_rule r)] without case-analysing first.  (And up to equality, we get the same result.)  *)

  (* TODO: consider placement *)
  Definition TT_Spec_signature_inclusion_of_rule
      {T : Type_Theory_Spec σ} (r : TTS_Rule T)
    : Signature_Map (TTS_signature_of_rule r) 
                    (Signature_of_TT_Spec T).
  Proof.
    simple refine (_;_).
    - intros s_isob_lt.
      exact (pr1 s_isob_lt ; fst (pr2 (s_isob_lt))).
      (* TODO: introduce access functions for the signature components above? *)
    - intros s. exact idpath.
  Defined.

  Definition Raw_TT_of_TT_Spec (T : Type_Theory_Spec σ)
    : Raw_Type_Theory (Signature_of_TT_Spec T).
  (* TODO: downstream, since this needs to add in the standard raw rules.  Possibly also downstream [Signature_of_TT_Spec]. *)
  Proof.
    (* First group: the structural rules *)
    refine (Family.Sum (Structural_Rules _) _).
    refine (Family.Sum _ _).
    (* Second group: the explicitly-given logical rules *)
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
    (* Third group: the congruence rules for the type-/term- operations *)
    - exists { r : TTS_Rule T & is_obj_HJF (TTS_hjf_of_rule r) }.
      intros [r Hr].
      refine (Raw_Rule_of_Rule_Spec _ _).
      + simple refine
        (associated_congruence_rule_spec
           _ (Fmap_Rule_Spec _ (TTS_rule_spec r)) _ _ _ _).
        * apply TT_Spec_signature_inclusion_of_rule.
        * exact Hr.
        * exact (r;Hr). (* head symbol of original rule *)
        * apply idpath.
        * apply idpath.
      + intros []. (* no overall head symbol, since congruence is an equality rule *)
  Defined.

  Definition Derivation_from_TT_Spec (T : Type_Theory_Spec σ)
    : Judgt_Instance (Signature_of_TT_Spec T) -> Type
  := Derivation_from_Raw_TT (Raw_TT_of_TT_Spec T).

End Derivability_from_TT_Spec.
