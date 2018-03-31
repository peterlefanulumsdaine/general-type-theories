Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.Arity.
Require Import Raw.Syntax.Signature.
Require Import Raw.Syntax.Context.
Require Import Raw.Syntax.Judgement.
Require Import Raw.Syntax.Metavariable.

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

End FlatRule.

Section FlatTypeTheory.

  Context {σ : shape_system}.

  Definition flat_type_theory (Σ : signature σ) : Type
     := family (flat_rule Σ).

End FlatTypeTheory.

Arguments closure_system {_ _} _.


Section SignatureMaps.

  Context {σ : shape_system}.

  Local Definition fmap {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
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

  Definition fmap_flat_type_theory {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_type_theory Σ -> flat_type_theory Σ'.
  Proof.
    apply Family.fmap, fmap, f.
  Defined.
  
End SignatureMaps.

  

