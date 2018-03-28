Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Raw.Signature.
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

End FlatRule.

Section Flat_Type_Theory.

  Context {σ : shape_system}.

  Definition flat_type_theory (Σ : signature σ) : Type
     := family (flat_rule Σ).

(*  Definition fmap_flat_type_theory {Σ Σ'} (f : Signature.map Σ Σ')
     : flat_type_theory Σ -> flat_type_theory Σ'.
  Proof.
  Defined. *)

End Flat_Type_Theory.

Arguments closure_system {_ _} _.
