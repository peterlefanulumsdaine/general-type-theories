Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.SignatureMap.
Require Import Raw.Theory.
Require Import WellFormed.Rule.

(** Main definition in this file: [Type_Theory], the data one gives to specify a type theory (but before typechecking it) *)

Section Type_Theories.

  Context {σ : shape_system}.

  Record Type_Theory
  := {
  (* The family of _rules_, with their object-premise arities and conclusion forms specified *)
    TT_rule_index :> family (Judgement.hypothetical_form * arity σ)
  (* the judgement form of the conclusion of each rule *)
  ; TT_hjf_of_rule : TT_rule_index -> Judgement.hypothetical_form
    := fun i => fst (TT_rule_index i)
  (* the arity of the arguments (i.e. the *object* premises only) of each rule *)
  ; TT_arity_of_rule : TT_rule_index -> arity _
    := fun i => snd (TT_rule_index i)
  (* the ordering on rules.  TODO: will probably need to add well-foundedness. QUESTION: any reason for it to be Prop-valued, or could we just let it be type-valued? *)
  ; TT_lt : TT_rule_index -> TT_rule_index -> Type
  (* the signature over which each rule can be written *)
  ; TT_signature_of_rule : TT_rule_index -> signature σ
    := fun i => Family.fmap
        (fun (ja : Judgement.hypothetical_form * arity σ) => (Judgement.class_of (fst ja), snd ja))
        (Family.subfamily TT_rule_index
          (fun j => Judgement.is_object (TT_hjf_of_rule j) * TT_lt j i))
  (* the actual rule specification of each rule *)
  ; TT_rule
    : forall i : TT_rule_index,
        rule
          (TT_signature_of_rule i)
          (TT_arity_of_rule i)
          (TT_hjf_of_rule i)
  }.

  Definition Signature_of_Type_Theory (T : Type_Theory)
    : signature σ.
  Proof.
    (* symbols are given by the object-judgement rules of T *)
    exists {r : T & Judgement.is_object (TT_hjf_of_rule _ r)}.
    intros r_H. set (r := pr1 r_H).
    split.
    - exact (Judgement.class_of (TT_hjf_of_rule _ r)).
    - exact (TT_arity_of_rule _ r).
  Defined.
    (* NOTE: it is tempting to case-analyse here and say 
      “when r is an object rule, use [(Judgement.class_of …, TT_arity_of_rule …)];
       in case r is an equality rule, use reductio ad absurdum with Hr.” 
     But we get stronger reduction behaviour by just taking [(Judgement.class_of …, TT_arity_of_rule …)] without case-analysing first.  (And up to equality, we get the same result.)  *)

  Definition Type_Theory_signature_inclusion_of_rule
      {T : Type_Theory} (r : T)
    : Signature_Map (TT_signature_of_rule _ r) 
                    (Signature_of_Type_Theory T).
  Proof.
    simple refine (_;_).
    - intros s_isob_lt.
      exact (pr1 s_isob_lt ; fst (pr2 (s_isob_lt))).
      (* TODO: introduce access functions for the signature components above? *)
    - intros s. apply idpath.
  Defined.

End Type_Theories.

Arguments Type_Theory _ : clear implicits.
Arguments TT_rule_index {_} _.
Arguments TT_hjf_of_rule {_ _} _.
Arguments TT_arity_of_rule {_ _} _.
Arguments TT_lt {_ _} _ _.
Arguments TT_signature_of_rule {_ _} _.
Arguments TT_rule {_ _} _.


Section Derivability_from_Type_Theory.

  Context {σ : shape_system}.

  Local Definition flatten (T : Type_Theory σ)
    : flat_type_theory (Signature_of_Type_Theory T).
  Proof.
    refine (_ + _).
    (* First: the explicitly-given logical rules *)
    - exists (TT_rule_index T).
      intros r.
      refine (flatten _ _).
      + (* translate rules up to the full signature *)
        refine (Fmap_rule _ (TT_rule r)).
        apply Type_Theory_signature_inclusion_of_rule.
      + (* pick their symbol in the full signature, if applicable *)
        intros r_obj.
        exists (r; r_obj).
        split; apply idpath.
    (* Second: associated congruence rules for the object-judgement logical rules. *)
    - exists { r : T & Judgement.is_object (TT_hjf_of_rule r) }.
      intros [r Hr].
      refine (flatten _ _).
      + simple refine
        (associated_congruence_rule
           (Fmap_rule _ (TT_rule r)) _ _ _ _).
        * apply Type_Theory_signature_inclusion_of_rule.
        * exact Hr.
        * exact (r;Hr). (* head symbol of original rule *)
        * apply idpath.
        * apply idpath.
      + intros []. (* no head symbol, since congs are equality rules *)
  Defined.

  Definition Derivation_from_Type_Theory (T : Type_Theory σ) H
    : judgement_total (Signature_of_Type_Theory T) -> Type
  := Derivation_from_Flat_Type_Theory (flatten T) H.

End Derivability_from_Type_Theory.
