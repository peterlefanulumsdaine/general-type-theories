Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.SyntaxLemmas.

Section FlatRule.

  Context {σ : shape_system}.
  Context (Σ : signature σ).

  (* TODO: Is it right that we allow arbitrary judgements, or should we allow
     only _hypothetical_ judgements? *)
  Record flat_rule
  :=
    { flat_rule_metas : arity _
    ; flat_rule_premises :
        family (judgement_total (Metavariable.extend Σ flat_rule_metas))
    ; flat_rule_conclusion :
        (judgement_total (Metavariable.extend Σ flat_rule_metas))
    }.

  Local Definition closure_system (R : flat_rule)
    : Closure.system (judgement_total Σ).
  Proof.
    exists { Γ : raw_context Σ &
                 Metavariable.instantiation (flat_rule_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Family.fmap _ (flat_rule_premises R)).
      apply (Metavariable.instantiate_judgement _ I).
    - apply (Metavariable.instantiate_judgement _ I).
      apply (flat_rule_conclusion R).
  Defined.

End FlatRule.

Arguments closure_system {_ _} _.

Section SignatureMaps.

  Context `{Funext} {σ : shape_system}.

  Local Definition fmap
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_rule Σ -> flat_rule Σ'.
  Proof.
    intros R.
    exists (flat_rule_metas _ R).
    - refine (Family.fmap _ (flat_rule_premises _ R)).
      apply fmap_judgement_total.
      apply Metavariable.fmap1, f.
    - refine (fmap_judgement_total _ (flat_rule_conclusion _ R)).
      apply Metavariable.fmap1, f.
  Defined.

  Local Definition fmap_closure_system 
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
        (R : flat_rule Σ)
    : Family.map_over (Closure.fmap (fmap_judgement_total f))
        (closure_system R)
        (closure_system (fmap f R)).
  Proof.
    apply Family.Build_map'.
    intros [Γ I_R].
    exists (Context.fmap f Γ ; fmap_instantiation f I_R).
    apply Closure.rule_eq.
    - simple refine (Family.eq _ _). { apply idpath. }
      cbn. intros i. apply inverse, fmap_instantiate_judgement.
    - cbn. apply inverse, fmap_instantiate_judgement.
  Defined.

End SignatureMaps.
