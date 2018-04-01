Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.CongruenceRule.

(** Main definition in this file: [Type_Theory], the data one gives to specify a type theory (but before typechecking it) *)

Section TypeTheory.

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
  (* the ordering on rules *)
  ; TT_lt : well_founded_order TT_rule_index
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
  (* TODO: consider making this a coercion? *)

  Definition Type_Theory_signature_inclusion_of_rule
      {T : Type_Theory} (r : T)
    : Signature.map (TT_signature_of_rule _ r) 
                    (Signature_of_Type_Theory T).
  Proof.
    simple refine (_;_).
    - intros s_isob_lt.
      exact (pr1 s_isob_lt ; fst (pr2 (s_isob_lt))).
      (* TODO: introduce access functions for the signature components above? *)
    - intros s. apply idpath.
  Defined.

  (* NOTE: could easily be generalised to give the sub-type-theory on any down-closed subset of the rules, if that’s ever needed. *)
  Definition sub_type_theory_below_rule (T : Type_Theory) (i : T)
    : Type_Theory.
  Proof.
    simple refine (Build_Type_Theory _ _ _ ).
    - refine (Family.subfamily (TT_rule_index T) _).
      intros j. exact (TT_lt _ j i).
    - refine (WellFounded.pullback _ (TT_lt T)).
      exact (projT1).
    - cbn. intros [j lt_j_i].
      refine (Rule.fmap _ (TT_rule _ j)).
      apply Family.map_fmap.
      simple refine (_;_).
      + intros [k [k_obj lt_k_j]].
        simple refine (_;_).
        * exists k. apply (transitive _ _ j); assumption.
        * cbn. split; assumption.
      + intros ?; apply idpath.
  Defined.

  (* NOTE: in fact, this map should be an isomorphism *)
  Definition signature_of_sub_type_theory (T : Type_Theory) (i : T)
    : Signature.map
        (Signature_of_Type_Theory (sub_type_theory_below_rule T i))
        (TT_signature_of_rule _ i).
  Proof.
    simple refine (_;_).
    - intros [[j lt_j_i] j_obj]. exists j. split; assumption.
    - intros ?; apply idpath.
  Defined.

End TypeTheory.

Arguments Type_Theory _ : clear implicits.
Arguments TT_rule_index {_} _.
Arguments TT_hjf_of_rule {_ _} _.
Arguments TT_arity_of_rule {_ _} _.
Arguments TT_lt {_ _}.
Arguments TT_signature_of_rule {_ _} _.
Arguments TT_rule {_ _} _.


Section Flattening.

  Context {σ : shape_system}.

  Local Definition flatten (T : Type_Theory σ)
    : flat_type_theory (Signature_of_Type_Theory T).
  Proof.
    refine (_ + _).
    (* First: the explicitly-given logical rules *)
    - exists (TT_rule_index T).
      intros r.
      refine (Rule.flatten _ _).
      + (* translate rules up to the full signature *)
        refine (Rule.fmap _ (TT_rule r)).
        apply Type_Theory_signature_inclusion_of_rule.
      + (* pick their symbol in the full signature, if applicable *)
        intros r_obj.
        exists (r; r_obj).
        split; apply idpath.
    (* Second: associated congruence rules for the object-judgement logical rules. *)
    - exists { r : T & Judgement.is_object (TT_hjf_of_rule r) }.
      intros [r Hr].
      refine (Rule.flatten _ _).
      + simple refine
        (CongruenceRule.associated
           (Rule.fmap _ (TT_rule r)) _ _ _ _).
        * apply Type_Theory_signature_inclusion_of_rule.
        * exact Hr.
        * exact (r;Hr). (* head symbol of original rule *)
        * apply idpath.
        * apply idpath.
      + intros []. (* no head symbol, since congs are equality rules *)
  Defined.

End Flattening.
