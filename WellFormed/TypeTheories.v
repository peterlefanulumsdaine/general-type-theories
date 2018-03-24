Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.DeductiveClosure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMaps.
Require Import Raw.TypeTheories.
Require Import WellFormed.Rules.

(** Main definition in this file: [Type_Theory_Spec], the data one gives to specify a type theory (but before typechecking it) *)

Section TTSpecs.

  Context {σ : Shape_System}.

  Record Type_Theory_Spec
  := {
  (* The family of _rules_, with their object-premise arities and conclusion forms specified *)
    TTS_Rule : Family (Hyp_Judgt_Form * Arity σ * Shape σ)
  (* the judgement form of the conclusion of each rule *)
  ; TTS_hjf_of_rule : TTS_Rule -> Hyp_Judgt_Form
    := fun i => fst (fst (TTS_Rule i))
  (* the arity of the arguments (i.e. the *object* premises only) of each rule *)
  ; TTS_arity_of_rule : TTS_Rule -> Arity _
    := fun i => snd (fst (TTS_Rule i))
  (* the shape of the conclusion of each rule *)
  ; TTS_concl_shape_of_rule : TTS_Rule -> Shape σ
    := fun i => snd (TTS_Rule i)
  (* the ordering on rules.  TODO: will probably need to add well-foundedness. QUESTION: any reason for it to be Prop-valued, or could we just let it be type-valued? *)
  ; TTS_lt : TTS_Rule -> TTS_Rule -> Type
  (* the signature over which each rule can be written *)
  ; TTS_signature_of_rule : TTS_Rule -> Signature σ
    := fun i => Fmap_Family
        (fun jaγ => ( class_of_HJF (fst (fst jaγ))
                   , Family.Sum (snd (fst jaγ)) (simple_arity (snd jaγ))))
        (Subfamily TTS_Rule
          (fun j => is_obj_HJF (TTS_hjf_of_rule j) * TTS_lt j i))
  (* the actual rule specification of each rule *)
  ; TTS_rule_spec
    : forall i : TTS_Rule,
        Rule_Spec
          (TTS_signature_of_rule i)
          (TTS_arity_of_rule i)
          (TTS_concl_shape_of_rule i)
          (TTS_hjf_of_rule i)
  }.

  Definition Signature_of_TT_Spec (T : Type_Theory_Spec)
    : Signature σ.
  Proof.
    (* symbols are given by the object-judgement rules of T *)
    exists {r : TTS_Rule T & is_obj_HJF (TTS_hjf_of_rule _ r)}.
    intros r_H. set (r := pr1 r_H).
    split.
    - exact (class_of_HJF (TTS_hjf_of_rule _ r)).
    - exact (TTS_arity_of_rule _ r
            + simple_arity (TTS_concl_shape_of_rule _ r)).
  Defined.
    (* NOTE: it is tempting to case-analyse here and say 
      “when r is an object rule, use [(class_of_HJF …, TTS_arity_of_rule …)];
       in case r is an equality rule, use reductio ad absurdum with Hr.” 
     But we get stronger reduction behaviour by just taking [(class_of_HJF …, TTS_arity_of_rule …)] without case-analysing first.  (And up to equality, we get the same result.)  *)

  Definition TT_Spec_signature_inclusion_of_rule
      {T : Type_Theory_Spec} (r : TTS_Rule T)
    : Signature_Map (TTS_signature_of_rule _ r) 
                    (Signature_of_TT_Spec T).
  Proof.
    simple refine (_;_).
    - intros s_isob_lt.
      exact (pr1 s_isob_lt ; fst (pr2 (s_isob_lt))).
      (* TODO: introduce access functions for the signature components above? *)
    - intros s. exact idpath.
  Defined.

End TTSpecs.

Arguments Type_Theory_Spec _ : clear implicits.
Arguments TTS_Rule {_} _.
Arguments TTS_hjf_of_rule {_ _} _.
Arguments TTS_arity_of_rule {_ _} _.
Arguments TTS_concl_shape_of_rule {_ _} _.
Arguments TTS_lt {_ _} _ _.
Arguments TTS_signature_of_rule {_ _} _.
Arguments TTS_rule_spec {_ _} _.


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
