Require Import HoTT.
Require Import Auxiliary.General.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.

(** A _flat rule_ is the simplest analysis of a rule of type theory:

- a collection of judgements as premises and conclusion,
- written in some metavariable extension of the ambient signature,
- yielding, for each instantiation of the metavariables, a closure
  condition on judgements.

This is just what’s required to define derivations and the typing relations.

Using those, we will then be able to define _well-presented_ rules,
which will carry extra structure ensuring the resulting typing relations
are well-behaved.
*)

Section FlatRule.

  Context {σ : scope_system}.

  (* TODO: Is it right that we allow arbitrary judgements, or should we allow
     only _hypothetical_ judgements? *)
  Record flat_rule {Σ : signature σ}
  :=
    { flat_rule_metas : arity _
    ; flat_rule_premise :
        family (judgement (Metavariable.extend Σ flat_rule_metas))
    ; flat_rule_conclusion :
        (judgement (Metavariable.extend Σ flat_rule_metas))
    }.

  Global Arguments flat_rule _ : clear implicits.

  Local Lemma eq {Σ : signature σ}
      {R R' : flat_rule Σ}
      (e_metas : flat_rule_metas R = flat_rule_metas R')
      (e_premises
       : transport (fun a => family (_ (_ _ a))) e_metas
                   (flat_rule_premise R)
         = flat_rule_premise R')
      (e_conclusion
       : transport (fun a => judgement (_ _ a)) e_metas
                   (flat_rule_conclusion R)
         = flat_rule_conclusion R')
    : R = R'.
  Proof.
    destruct R, R'; cbn in *.
    destruct e_metas, e_premises, e_conclusion.
    apply idpath.
  Defined.

  Local Definition fmap
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_rule Σ -> flat_rule Σ'.
  Proof.
    intros R.
    exists (flat_rule_metas R).
    - refine (Family.fmap _ (flat_rule_premise R)).
      apply Judgement.fmap.
      apply Metavariable.fmap1, f.
    - refine (Judgement.fmap _ (flat_rule_conclusion R)).
      apply Metavariable.fmap1, f.
  Defined.

  Context `{Funext}.

  Local Lemma fmap_idmap
      {Σ : signature σ} (R : flat_rule Σ)
    : fmap (Signature.idmap _) R = R.
  Proof.
    simple refine (eq _ _ _).
    - apply idpath.
    - cbn.
      eapply concat.
      { rapply @ap_1back.
        eapply concat. { apply ap, Metavariable.fmap1_idmap. }
        apply path_forall; intros i.
        apply Judgement.fmap_idmap. }
      apply Family.fmap_idmap.
    - cbn.
      eapply concat. 2: { apply Judgement.fmap_idmap. }
      apply ap10, ap. apply Metavariable.fmap1_idmap.
  Defined.

  Local Lemma fmap_compose
      {Σ Σ' Σ'' : signature σ}
      (f : Signature.map Σ Σ') (f' : Signature.map Σ' Σ'')
      (R : flat_rule Σ)
    : fmap (Signature.compose f' f) R
      = fmap f' (fmap f R).
  Proof.
    simple refine (eq _ _ _).
    - apply idpath.
    - cbn.
      eapply concat. 2: { apply Family.fmap_compose. }
      rapply @ap_1back.
      eapply concat. { apply ap, Metavariable.fmap1_compose. }
      apply path_forall; intros i.
      apply Judgement.fmap_compose.
    - cbn.
      eapply concat. 2: { apply Judgement.fmap_compose. }
      apply ap10, ap, Metavariable.fmap1_compose.
  Defined.

End FlatRule.

Section ClosureSystem.

  Context {σ : scope_system}.

  Local Definition closure_system {Σ : signature σ} (R : flat_rule Σ)
    : Closure.system (judgement Σ).
  Proof.
    exists { Γ : raw_context Σ &
                 Metavariable.instantiation (flat_rule_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Family.fmap _ (flat_rule_premise R)).
      apply (Judgement.instantiate Γ I).
    - apply (Judgement.instantiate Γ I).
      apply (flat_rule_conclusion R).
  Defined.

  Context `{Funext}.

  (** Note: unlike some similar lemmas, this really is a non-invertible map in general, i.e. a “lax naturality” not naturality. *)
  Local Definition closure_system_fmap
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
        (R : flat_rule Σ)
    : Family.map_over (Closure.rule_fmap (Judgement.fmap f))
        (closure_system R)
        (closure_system (fmap f R)).
  Proof.
    apply Family.Build_map'.
    intros [Γ I_R].
    exists (Context.fmap f Γ ; instantiation_fmap f I_R).
    apply Closure.rule_eq.
    - simple refine (Family.eq _ _). { apply idpath. }
      cbn; intros i.
      apply inverse, Judgement.fmap_instantiate.
    - cbn. apply inverse, Judgement.fmap_instantiate.
  Defined.

  Local Definition closure_system_fmap'
    {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    {R} {R'} (e : fmap f R = R')
  : Family.map_over (Closure.rule_fmap (Judgement.fmap f))
      (closure_system R)
      (closure_system R').
  Proof.
    destruct e. apply closure_system_fmap.
  Defined.

End ClosureSystem.

(** Instantiations?  The interaction between flat rules and instantiations — in particular, the interaction with [FlatRule.closure_system] — can’t be given here, since it depends on structural rules, at least on the rule for variable-renaming.  So see [Typing.FlatTypeTheory] downstream for lemmas on this, and the comments at  [instantiate_flat_rule_closure_system] there for a more detailed explanation. *)

(* NOTE: what we could give in this file, and should if it’s needed anywhere, would be the “functoriality of flat rules under instantiations”: i.e. translating a flat rule over [Σ+a] to a flat rule over [Σ], using [Judgement.instantiate]. *)

Section Congruence.

  Context `{Funext} {σ : scope_system}.

  Definition flat_congruence_rule
      {Σ : signature σ}
      (R : flat_rule Σ)
      (R_obj : Judgement.is_object (form_of_judgement (flat_rule_conclusion R)))
    : flat_rule Σ.
  Proof.
    assert (inl : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inl. }
    assert (inr : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inr. }
    exists (flat_rule_metas R + flat_rule_metas R).
    - (* premises *)
      refine (_ + _ + _).
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inl.
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inr.
      + exists {p : flat_rule_premise R
                    & Judgement.is_object
                        (form_of_judgement (flat_rule_premise R p))}.
        intros [p p_obj].
        set (J := flat_rule_premise R p).
        fold J in p_obj.
        exists (Context.fmap inl (context_of_judgement J)).
        simple refine (combine_hypothetical_judgement _ _ _ _).
        * exact (fmap_hypothetical_judgement inl J).
        * exact (fmap_hypothetical_judgement inr J).
        * apply idpath.
        * apply p_obj.
    - (* conclusion *)
      set (J := flat_rule_conclusion R).
      apply (combine_judgement (Judgement.fmap inl J) (Judgement.fmap inr J)).
      + apply idpath.
      + apply R_obj.
  Defined.

End Congruence.
