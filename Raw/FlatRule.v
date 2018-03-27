Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Raw.Presyntax.
Require Import Raw.Context.
Require Import Raw.Judgement.
Require Import Raw.Metavariable.

Section FlatRule.

  Context {σ : shape_system}.
  Context (Σ : signature σ).

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
      apply (Metavariable.instantiate_judgement I).
    - apply (Metavariable.instantiate_judgement I).
      apply (flat_rule_conclusion R).
  Defined.

  Definition raw_type_theory := family flat_rule.

End FlatRule.

Arguments closure_system {_ _} _.
