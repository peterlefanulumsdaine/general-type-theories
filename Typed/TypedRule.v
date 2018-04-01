Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.AlgebraicExtension.
Require Import Raw.Rule.
Require Import Raw.TypeTheory.
Require Import Typed.Derivation.

(** In this file: definition of well-typedness of an algebraic extension, and a (well-presented) rule. *)

Section Welltypedness.

  Context {σ : shape_system}.

  Definition is_well_typed_algebraic_extension
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    refine (Derivation_Judgt_Bdry_Instance _ (AlgebraicExtension.judgement_boundary r) _).
    - (* ambient type theory to typecheck premise [p] in *)
      simple refine (fmap_flat_type_theory _ T).
      apply include_symbol.
    - (* open hypotheses to allow in the derivation *)
      exists {i : ae_premise A & ae_lt _ i r }.
      intros [i lt_i_r].
      apply (judgement_of_premise i).
      + apply Metavariable.fmap2.
        simple refine (_;_).
        * intros [j lt_j_i].
          simpl. exists j. apply (WellFounded.transitive (ae_lt A) _ i r); assumption.
        * intro; apply idpath.
      + intros H_i_obj.
        destruct i as [ i | i ]; simpl in i.
        * (* case: i an object premise *)
          simple refine (_;_). 
          -- apply include_metavariable. exists i. assumption.
          -- split; apply idpath.
        * (* case: i an equality premise *)
          destruct H_i_obj. (* ruled out by assumption *)
  Defined.
  (* NOTE: when checking we want to add the earlier premises of [A] to [T], and typecheck [r] over that.  There are (at least) three ways to do this:
  (1) take earlier rules just as judgements, and allow them as hypotheses in the derivation;
  (2) take earlier rules as judgements, then add rules to [T] giving these judgements as axioms;
  (3) give the extension of [T] by the preceding part of [A] as a type theory, i.e. turn rules of [A] into actual *rules*, with the variables of their contexts turned into term premises.
  
  In any case we must first translate [T] up to the extended signature of [R].
  
  (1) would nicely fit into the monadic view of derivations.
  (3) would nicely factorise into “take initial segment of an alg ext”, and “extend TT by an alg ext”; also avoids the need to frequently use “cut” when invoking the earlier premises in the derivations
  
  We currently take option (1).
  *)

  Definition is_well_typed_rule
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} {hjf_concl}
      (R : rule Σ a hjf_concl)
    : Type.
  Proof.
    refine (is_well_typed_algebraic_extension T (rule_premise R) * _).
    (* well-typedness of conclusion *)
    refine (Derivation_Judgt_Bdry_Instance _ (Rule.conclusion_boundary R) _).
    - (* ambient type theory to typecheck premise [p] in *)
      simple refine (fmap_flat_type_theory _ T).
      apply include_symbol.
    - (* open hypotheses to allow in the derivation *)
      exists (rule_premise R).
      intros i. apply (judgement_of_premise i).
      + apply Metavariable.fmap2.
        apply Family.inclusion.
      + intros H_i_obj.
        destruct i as [ i | i ]; simpl in i.
        * (* case: i an object premise *)
          simple refine (_;_). 
          -- apply include_metavariable. exact i.
          -- split; apply idpath.
        * (* case: i an equality premise *)
          destruct H_i_obj. (* ruled out by assumption *)
  Defined.

End Welltypedness.