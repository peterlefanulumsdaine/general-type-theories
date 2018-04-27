Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.AlgebraicExtension.
Require Import Raw.RawRule.
Require Import Raw.FlatRule.
Require Import Raw.FlatTypeTheory.
Require Import Raw.FlatTypeTheoryMap.
Require Import Typed.TypedFlatRule.

(** In this file: definition of well-typedness of an algebraic extension, and a (well-presented) rule. *)

Section WellTypedRule.

  Context {σ : shape_system}.

  Definition is_well_typed_algebraic_extension
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    assert (H : family (judgement_total (ae_signature A r))).
    { (* open hypotheses to allow in the derivation of each premise *)
      exists {i : ae_premise A & ae_lt _ i r }.
      intros [i lt_i_r].
      apply (AlgebraicExtension.judgement_of_premise i).
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
    }
    set (r_bdry := AlgebraicExtension.judgement_boundary r).
    refine (forall (i : presupposition_of_boundary r_bdry),
               FlatTypeTheory.derivation
                 (FlatTypeTheory.fmap include_symbol T)
                 H
                 (presupposition_of_boundary _ i)).
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
    exact (forall (i : presupposition_of_boundary (RawRule.conclusion_boundary R)),
               FlatTypeTheory.derivation
                 (FlatTypeTheory.fmap include_symbol T)
                 (AlgebraicExtension.flatten (rule_premise R))
                 (presupposition_of_boundary _ i)).
  Defined.

End WellTypedRule.

Section Flattening.

  Context {σ : shape_system} `{Funext}.

  Definition weakly_well_typed_flatten
      {Σ : signature σ} {T : flat_type_theory Σ}
      {a} {hjf_concl}
      {R : rule Σ a hjf_concl}
      (T_WT : is_well_typed_rule T R)
      (Sr : Judgement.is_object hjf_concl ->
        {S : Σ.(family_index) &
        (symbol_arity S = a) * (symbol_class S = Judgement.class_of hjf_concl)})
    : TypedFlatRule.weakly_well_typed T (RawRule.flatten R Sr).
  Proof.
    apply snd in T_WT.
    intros i.
    refine (Closure.graft' (T_WT i) _ _).
    - unfold presupposition.
      apply ap10.
      assert (e :
        RawRule.conclusion_boundary R
        =
        boundary_of_judgement
          (pr2 (flat_rule_conclusion _ (RawRule.flatten R Sr)))).
      { recursive_destruct hjf_concl; apply idpath. }
      (* TODO: perhaps try to improve defs of boundary/judgt slots
       so that the above computes on the nose? *)
      destruct e. apply idpath.
    - clear i. intros i.
      exact (Closure.hypothesis _ (_+_) (inl i)).
  Defined.
  (* TODO: in fact, we should be able to extend this to showing
   that [flatten R] is _strongly_ well-typed. *)
  
 End Flattening.