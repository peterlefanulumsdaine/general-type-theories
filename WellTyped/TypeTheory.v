Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.
Require Import Raw.Theory.
Require Import Raw.SignatureMap.
Require Import WellFormed.Rule.
Require Import WellFormed.TypeTheory.

(** In this file: definition of well-typedness of a rule, and of a type-theory. *)

Section Welltypedness.

  Context {σ : shape_system}.

  (* TODO: move upstream! *)
  Definition Build_Family_Map' {X} {K L : family X}
    : (forall i:K, {j:L & L j = K i})
      -> Family.map K L.
  Proof.
    intros f.
    exists (fun i => pr1 (f i)).
    intros i; exact (pr2 (f i)).
  Defined.

  Arguments Judgement.hypothetical_boundary : simpl nomatch.
  Arguments Judgement.hypothetical_boundary : simpl nomatch.

  (* TODO: move upstream; consider name! *)
  (* This is the special case of [presup_slots_from_boundary] for object judgements.
    It is abstracted out because it’s used twice: directly for object judgements, and as part of the case for equality judgements.
    In fact it’s almost trivial, so could easily be inlined; but conceptually it is the same thing both times, and in type theory with more judgements, it could be less trivial, so we keep it factored out. *)
  Definition obj_presup_slots_from_boundary
    {cl : syntactic_class} (i : Judgement.object_boundary_slot cl)
    : Family.map
        (Judgement.object_boundary_slot (Judgement.object_boundary_slot cl i))
        (Judgement.object_boundary_slot cl).
  Proof.
    apply Build_Family_Map'. intros j.
    destruct cl as [ | ]; cbn in i.
    (* Ty: nothing to do, no objects in boundary *)
    - destruct i.
    (* Tm: i must be type, so again nothing left, no j in its boundary *)
    - destruct i as [[] |]; destruct j.
  Defined.

  (* TODO: move upstream; consider name! *)
  Definition presup_slots_from_boundary
    {hjf : Judgement.hypothetical_form} (i : Judgement.boundary_slot hjf)
    : Family.map
        (Judgement.slot (form_object (Judgement.boundary_slot hjf i)))
        (Judgement.boundary_slot hjf).
  Proof.
    apply Build_Family_Map'.
    intros [ j | ].
    - (* case: j in boundary part of presupposition *)
      destruct hjf as [ cl | cl ].
      + (* original hjf is object judgement *)
        exists (obj_presup_slots_from_boundary i j).
        apply (Family.map_commutes _ j).
      + (* original hjf is equality judgement *)
        destruct i as [ [i' | ] | ].
        * (* i is in shared bdry of LHS/RHS *)
          cbn in j.
          exists (Some (Some (obj_presup_slots_from_boundary i' j))).
          apply (Family.map_commutes _ j).
        * (* i is RHS *)
          exists (Some (Some j)). apply idpath.
        * (* i is LHS *)
          exists (Some (Some j)). apply idpath.
    - (* case: j is head of presupposition *)
      exists i. apply idpath.
  Defined.
  
  (* TODO: move upstream, right to [Syntax] even? *)
  Definition Presup_of_Judgt_Bdry_Instance
      {Σ : signature σ} {jf} (jbi : Judgement.boundary Σ jf)
    : family (judgement_total Σ).
  Proof.
    destruct jf as [ | hjf].
    - (* context judgement: no boundary *)
      apply Family.empty.
    - (* hyp judgement: presups are the context,
                        plus the slots of the hyp boundary *)
      apply Family.adjoin.
      + exists (Judgement.boundary_slot hjf).
        intros i.
        exists (form_hypothetical (form_object ((Judgement.boundary_slot hjf) i))).
        exists (pr1 jbi).
        intros j.
        set (p := Family.map_commutes (presup_slots_from_boundary i) j).
        set (j' := presup_slots_from_boundary i j) in *.
        destruct p.
        exact (pr2 jbi j').
      + exists (form_context).
        exact (pr1 jbi).
  Defined.

  (* TODO: move upstream to [TypingJudgements] *)
  (* TODO: consider making Signature_of_Type_Theory a coercion? *)
  (* TODO: consider naming conventions for types of the form “derivation of X from Y” *)
  (* TODO: think about use of “derivation” vs. “derivability”. *)
  Definition Derivation_Judgt_Bdry_Instance
      {Σ : signature σ} (T : flat_type_theory Σ)
      {jf} (jbi : Judgement.boundary Σ jf)
      (H : family (judgement_total Σ))
    : Type
  :=
    forall (i : Presup_of_Judgt_Bdry_Instance jbi),
      Derivation_from_Flat_Type_Theory T H (Presup_of_Judgt_Bdry_Instance _ i).

  (* TODO: upstream *)
  Definition extend {Σ : signature σ} {a : arity σ}
      (T : flat_type_theory Σ) (A : algebraic_extension Σ a)
    : flat_type_theory Σ.
  Proof.
  Admitted.
  
  (* TODO: upstream, maybe even into def of algebraic extension? *)
  (* TODO: rename [ae_arity_of_premise] to [ae_arity_for_premise] ? *)
  Definition ae_signature_for_premise {Σ : signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
  := (Metavariable.extend Σ (ae_arity_of_premise _ r)).

  (* TODO: upstream *)
  Definition ae_judgt_bdry_of_premise {Σ : signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
    : Judgement.boundary (ae_signature_for_premise r) (form_hypothetical (ae_hjf_of_premise _ r)).
  Proof.
    exists (ae_raw_context_of_premise _ r).
    apply (ae_hyp_bdry_of_premise).
  Defined.

  (* TODO: upstream; consider naming *)
  Definition include_symbol (Σ : signature σ) a
     : (Signature_Map Σ (Metavariable.extend Σ a)).
  Proof.
    exists Metavariable.include_symbol.
    intros; apply idpath.
  Defined.

Require Auxiliary.WellFounded.
  Definition is_well_typed_algebraic_extension
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    refine (Derivation_Judgt_Bdry_Instance _ (ae_judgt_bdry_of_premise r) _).
    - (* ambient type theory to typecheck premise [p] in *)
      simple refine (fmap_flat_type_theory _ T).
      apply include_symbol.
    - (* open hypotheses to allow in the derivation *)
      exists {i : ae_premise A & ae_lt _ i r }.
      intros [i lt_i_r].
      apply (judgement_of_premise i).
      + apply Fmap2_Metavariable_Extension.
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
    refine (is_well_typed_algebraic_extension T (premise R) * _).
    (* well-typedness of conclusion *)
    refine (Derivation_Judgt_Bdry_Instance _ (judgt_bdry_of_conclusion R) _).
    - (* ambient type theory to typecheck premise [p] in *)
      simple refine (fmap_flat_type_theory _ T).
      apply include_symbol.
    - (* open hypotheses to allow in the derivation *)
      exists (premise R).
      intros i. apply (judgement_of_premise i).
      + apply Fmap2_Metavariable_Extension.
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

  (* TODO: upstream to [WellFormed.TypeTheory] *)
  (* NOTE: could easily be generalised to give the sub-type-theory on any down-closed subset of the rules, if that’s ever needed. *)
  Definition sub_type_theory_below_rule (T : Type_Theory σ) (i : T)
    : Type_Theory σ.
  Proof.
    simple refine (Build_Type_Theory _ _ _ ).
    - refine (Family.subfamily (TT_rule_index T) _).
      intros j. exact (TT_lt j i).
    - refine (WellFounded.pullback _ (@TT_lt _ T)).
      exact (projT1).
    - cbn. intros [j lt_j_i].
      refine (Fmap_rule _ (TT_rule j)).
      apply Family.map_fmap.
      simple refine (_;_).
      + intros [k [k_obj lt_k_j]].
        simple refine (_;_).
        * exists k. apply (transitive _ _ j); assumption.
        * cbn. split; assumption.
      + intros ?; apply idpath.
  Defined.

  (* TODO: upstream to [WellFormed.TypeTheory] *)
  (* NOTE: should be moreover an isomorphism *)
  Definition signature_of_sub_type_theory (T : Type_Theory σ) (i : T)
    : Signature_Map
        (Signature_of_Type_Theory (sub_type_theory_below_rule T i))
        (TT_signature_of_rule i).
  Proof.
    simple refine (_;_).
    - intros [[j lt_j_i] j_obj]. exists j. split; assumption.
    - intros ?; apply idpath.
  Defined.

  Definition is_well_typed_type_theory (T : Type_Theory σ) : Type.
  Proof.
    refine (forall R : T, _).
    refine (is_well_typed_rule _ (TT_rule R)).
    refine (fmap_flat_type_theory _ _).
    Focus 2. { refine (@TypeTheory.flatten _ _).
      exact (sub_type_theory_below_rule T R). }
    Unfocus.
    apply signature_of_sub_type_theory.
  Defined.

End Welltypedness.

Section TypeTheory.

  Context {σ : shape_system}.

  Record type_theory : Type
  := { raw_type_theory_of_well_typed :> Type_Theory σ
     ; is_well_typed : is_well_typed_type_theory
                         raw_type_theory_of_well_typed }.

End TypeTheory.
