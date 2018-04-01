Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Closure.
Require Import Raw.Syntax.
Require Import Raw.Rule.
Require Import Raw.CongruenceRule.

(** Main definition in this file: [raw_type_theory], the data one gives to specify a type theory (but before typechecking it) *)

Section TypeTheory.

  Context {σ : shape_system}.

  Record raw_type_theory
  := {
  (* The family of _rules_, with their object-premise arities and conclusion forms specified *)
    tt_rule_data :> family (Judgement.hypothetical_form * arity σ)
  (* the judgement form of the conclusion of each rule *)
  ; tt_rule_form : tt_rule_data -> Judgement.hypothetical_form
    := fun i => fst (tt_rule_data i)
  (* the arity of the arguments (i.e. the *object* premises only) of each rule *)
  ; tt_rule_arity : tt_rule_data -> arity _
    := fun i => snd (tt_rule_data i)
  (* the ordering on rules *)
  ; tt_lt : well_founded_order tt_rule_data
  (* the signature over which each rule can be written *)
  ; tt_rule_signature : tt_rule_data -> signature σ
    := fun i => Family.fmap
        (fun (ja : Judgement.hypothetical_form * arity σ) => (Judgement.class_of (fst ja), snd ja))
        (Family.subfamily tt_rule_data
          (fun j => Judgement.is_object (tt_rule_form j) * tt_lt j i))
  (* the actual rule specification of each rule *)
  ; tt_rule
    : forall i : tt_rule_data,
        rule
          (tt_rule_signature i)
          (tt_rule_arity i)
          (tt_rule_form i)
  }.

  Local Definition signature (T : raw_type_theory)
    : signature σ.
  Proof.
    (* symbols are given by the object-judgement rules of T *)
    exists {r : T & Judgement.is_object (tt_rule_form _ r)}.
    intros r_H. set (r := pr1 r_H).
    split.
    - exact (Judgement.class_of (tt_rule_form _ r)).
    - exact (tt_rule_arity _ r).
  Defined.
    (* NOTE: it is tempting to case-analyse here and say 
      “when r is an object rule, use [(Judgement.class_of …, tt_rule_arity …)];
       in case r is an equality rule, use reductio ad absurdum with Hr.” 
     But we get stronger reduction behaviour by just taking [(Judgement.class_of …, tt_rule_arity …)] without case-analysing first.  (And up to equality, we get the same result.)  *)
  (* TODO: consider making this a coercion? *)

  Local Definition include_rule_signature
      {T : raw_type_theory} (r : T)
    : Signature.map (tt_rule_signature _ r) 
                    (signature T).
  Proof.
    simple refine (_;_).
    - intros s_isob_lt.
      exact (pr1 s_isob_lt ; fst (pr2 (s_isob_lt))).
      (* TODO: introduce access functions for the signature components above? *)
    - intros s. apply idpath.
  Defined.

  (* NOTE: could easily be generalised to give the sub-type-theory on any down-closed subset of the rules, if that’s ever needed. *)
  Local Definition subtheory (T : raw_type_theory) (i : T)
    : raw_type_theory.
  Proof.
    simple refine (Build_raw_type_theory _ _ _ ).
    - refine (Family.subfamily (tt_rule_data T) _).
      intros j. exact (tt_lt _ j i).
    - refine (WellFounded.pullback _ (tt_lt T)).
      exact (projT1).
    - cbn. intros [j lt_j_i].
      refine (Rule.fmap _ (tt_rule _ j)).
      apply Family.map_fmap.
      simple refine (_;_).
      + intros [k [k_obj lt_k_j]].
        simple refine (_;_).
        * exists k. apply (transitive _ _ j); assumption.
        * cbn. split; assumption.
      + intros ?; apply idpath.
  Defined.

  (* NOTE: in fact, this map should be an isomorphism *)
  Local Definition subtheory_signature (T : raw_type_theory) (i : T)
    : Signature.map
        (TypeTheory.signature (subtheory T i))
        (tt_rule_signature _ i).
  Proof.
    simple refine (_;_).
    - intros [[j lt_j_i] j_obj]. exists j. split; assumption.
    - intros ?; apply idpath.
  Defined.

End TypeTheory.

Arguments raw_type_theory _ : clear implicits.
Arguments tt_rule_data {_} _.
Arguments tt_rule_form {_ _} _.
Arguments tt_rule_arity {_ _} _.
Arguments tt_lt {_ _}.
Arguments tt_rule_signature {_ _} _.
Arguments tt_rule {_ _} _.


Section Flattening.

  Context {σ : shape_system}.

  Local Definition flatten (T : raw_type_theory σ)
    : flat_type_theory (signature T).
  Proof.
    refine (_ + _).
    (* First: the explicitly-given logical rules *)
    - exists (tt_rule_data T).
      intros r.
      refine (Rule.flatten _ _).
      + (* translate rules up to the full signature *)
        refine (Rule.fmap _ (tt_rule r)).
        apply include_rule_signature.
      + (* pick their symbol in the full signature, if applicable *)
        intros r_obj.
        exists (r; r_obj).
        split; apply idpath.
    (* Second: associated congruence rules for the object-judgement logical rules. *)
    - exists { r : T & Judgement.is_object (tt_rule_form r) }.
      intros [r Hr].
      refine (Rule.flatten _ _).
      + simple refine
        (CongruenceRule.associated
           (Rule.fmap _ (tt_rule r)) _ _ _ _).
        * apply include_rule_signature.
        * exact Hr.
        * exact (r;Hr). (* head symbol of original rule *)
        * apply idpath.
        * apply idpath.
      + intros []. (* no head symbol, since congs are equality rules *)
  Defined.

End Flattening.
