Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
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
  (* TODO: rename [ae_arity_of_rule] to [ae_arity_for_rule] ? *)
  Definition ae_signature_for_rule {Σ : signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
  := (Metavariable.extend Σ (ae_arity_of_rule _ r)).

  (* TODO: upstream *)
  Definition ae_judgt_bdry_of_rule {Σ : signature σ} {a}
      {A : algebraic_extension Σ a} (r : A)
    : Judgement.boundary (ae_signature_for_rule r) (form_hypothetical (ae_hjf_of_rule _ r)).
  Proof.
    exists (ae_raw_context_of_rule _ r).
    apply (ae_hyp_bdry_of_rule).
  Defined.

  (* TODO: upstream; consider naming *)
  Definition include_symbol (Σ : signature σ) a
     : (Signature_Map Σ (Metavariable.extend Σ a)).
  Proof.
    exists Metavariable.include_symbol.
    intros; apply idpath.
  Defined.

  Lemma ae_transitive {Σ : signature σ} {a} {A : algebraic_extension Σ a}
    : Transitive (ae_lt A).
  Admitted.  (* Needs to be added as assuption in [algebraic_extension]. *)

  (* TODO: upstream to [WellFormed.Rule]; 
           use this in [raw_rule_of_rule] (flattening);
           consider whether the flattening of the conclusion can also be covered by this. *)
  Lemma judgement_of_premise 
      {Σ : signature σ} {a} {A : algebraic_extension Σ a} (i : A)
      {Σ'} (f : Signature_Map (Metavariable.extend Σ (ae_arity_of_rule _ i)) Σ')
      (Sr : Judgement.is_object (ae_hjf_of_rule _ i) 
           -> { S : Σ'
             & (symbol_arity S = simple_arity (ae_proto_cxt_of_rule _ i))
             * (symbol_class S = Judgement.class_of (ae_hjf_of_rule _ i))})
   : judgement_total Σ'.
  Proof.
      exists (form_hypothetical (ae_hjf_of_rule _ i)).
      exists (Fmap_Raw_Context f (ae_raw_context_of_rule _ i)).
      apply Judgement.hypothetical_instance_from_boundary_and_head.
      + refine (Fmap_Hyp_Judgt_Bdry_Instance f _).
        apply ae_hyp_bdry_of_rule.
      + intro H_obj.
        destruct i as [ i_obj | i_eq ]; simpl in *.
        * (* case: i an object rule *)
          simple refine (raw_symbol' _ _ _).
          -- refine (Sr _).1. constructor.
          -- refine (snd (Sr _).2).
          -- set (e := (fst (Sr tt).2)^). destruct e.
             intro v. apply raw_variable.
             exact (coproduct_inj1 shape_is_sum v).
        * (* case: i an equality rule *)
          destruct H_obj. (* ruled out by assumption *)
  Defined.
   
  Definition is_well_typed_algebraic_extension
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    refine (Derivation_Judgt_Bdry_Instance _ (ae_judgt_bdry_of_rule r) _).
    - (* ambient type theory to typecheck premise [p] in *)
      simple refine (fmap_flat_type_theory _ T).
      apply include_symbol.
    - (* open hypotheses to allow in the derivation *)
      exists {i : ae_rule A & ae_lt _ i r }.
      intros [i lt_i_r].
      apply (judgement_of_premise i).
      + apply Fmap2_Metavariable_Extension.
        simple refine (_;_).
        * intros [j lt_j_i].
          simpl. exists j. apply (ae_transitive _ i); assumption.
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
  (* Roughly, we want to add the earlier rules of [A] to [T], and typecheck [r] over that.  There are (at least) three ways to do this:
    (1) take earlier rules just as judgements, and allow them as hypotheses in the derivation;
    (2) take earlier rules as judgements, then add rules to [T] giving these judgements as axioms;
    (3) actually give the extension of [T] by the preceding part of [A] as a type theory, i.e. turn rules of [A] into actual *rules*, with the variables of their contexts turned into term premises.  This option avoids extra use of the “cut” rule in derivations.

    In any case we must first translate [T] up to the extended signature of [R].

  (1) would nicely fit into the monadic view of derivations.
  (3) would nicely factorise into “take initial segment of an alg ext”, and “extend TT by an alg ext”.

  We currently take option (1).
  *)

  Definition Is_Well_Typed_Rule
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

End Welltypedness.