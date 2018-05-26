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
Require Import Typed.TypedFlatRule.

(** In this file: definition of well-typedness of an algebraic extension, and a (well-presented) rule. *)

Section WellTypedRule.

  Context {σ : shape_system}.

  (* TODO: upstream to [TypedAlgebraicExtension]. *)
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
    set (r_bdry := AlgebraicExtension.premise_boundary r).
    refine (forall (i : presupposition_of_boundary r_bdry),
               FlatTypeTheory.derivation
                 (FlatTypeTheory.fmap include_symbol T)
                 H
                 (presupposition_of_boundary _ i)).
  Defined.
  (* NOTE: when checking we want to add the earlier premises of [A] to [T], and typecheck [r] over that.  There are (at least) three ways to do this:
  (1) take earlier premises just as judgements, and allow them as hypotheses in the derivation;
  (2) take earlier premise as judgements, then add no-premise flat rules to [T], giving these judgements as axioms;
  (3) give the extension of [T] by the preceding part of [A] as a type theory, i.e. turn premises of [A] into genuine flat rules, with the variables of their contexts turned into term premises, and conclusion just the head of the given premise of [A].
  
  In any case we must first translate [T] up to the extended signature of [R].
  
  (1) would nicely fit into the monadic view of derivations.
  (3) would nicely factorise into “take initial segment of an alg ext”, and “extend TT by an alg ext”; also avoids the need to frequently use “cut” when invoking the earlier premises in the derivations
  
  We currently take option (1).
  *)

  (* TODO: consider naming.  Currently rather misleading: this is the type of derivations showing that the rule is well-formed, not “derivations of the rule” in the usual sense of derivations showing it’s a derivable rule. *) 
  Local Definition is_well_typed
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

Section Functoriality.

  Context {σ : shape_system} `{H_funext : Funext}.

  (* TODO: upstream *)
  Definition fmap_judgement_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} (B : Judgement.boundary Σ jf)
    : Judgement.boundary Σ' jf.
  Proof.
    destruct jf as [ | hjf].
    - exact B.
    - exists (Context.fmap f B.1).
      exact (fmap_hypothetical_boundary f B.2).
  Defined.
 
  Arguments fmap_judgement_total : simpl nomatch.
  Arguments fmap_judgement_boundary : simpl nomatch.
  Arguments presupposition_of_boundary : simpl nomatch.
  Arguments Judgement.boundary_slot_from_presupposition : simpl nomatch.

  (* TODO: upstream *)
  Definition presupposition_fmap_judgement_boundary
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {jf} (B : Judgement.boundary Σ jf)
    : Family.map
        (presupposition_of_boundary (fmap_judgement_boundary f B))
        (Family.fmap (fmap_judgement_total f) (presupposition_of_boundary B)).
  Proof.
    exists idmap.
    intros i.
    destruct jf as [ | hjf].
    - (* context *) destruct i. (* no presups *)
    - (* hyp *)
      recursive_destruct hjf; recursive_destruct i; try apply idpath;
        apply Judgement.eq_by_expressions;
        intros j; recursive_destruct j; apply idpath.
  Defined.

  (* TODO: upstream; consider name *)
  Lemma flat_type_theory_deduce_rule
      {Σ : signature σ} (T : flat_type_theory Σ)
      (r : T)
    : FlatTypeTheory.flat_rule_derivation T (T r).
  Proof.
  Admitted.

  (* TODO: upstream *)
  Lemma flat_type_theory_map_from_family_map
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
      (ff : Family.map_over (FlatRule.fmap f) T T')
    : FlatTypeTheory.map_over f T T'.
  Proof.
    intros R.
    refine (transport _ (Family.map_over_commutes ff R) _).
    apply flat_type_theory_deduce_rule.
  Defined.

  (* TODO: upstream; consider name *)
  Lemma family_map_to_fmap
      {X X'} (f : X -> X') (K : family X)
    : Family.map_over f K (Family.fmap f K).
  Proof.
    exists idmap.
    intros i; apply idpath.
  Defined.

  (* TODO: upstream; consider name *)
  Lemma flat_type_theory_map_to_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : flat_type_theory Σ)
    : FlatTypeTheory.map_over f T (FlatTypeTheory.fmap f T).
  Proof.
    apply flat_type_theory_map_from_family_map.
    apply family_map_to_fmap.
  Defined.

  Lemma flat_type_theory_fmap_derivation
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : flat_type_theory Σ} {H : family (judgement_total Σ)} {J}
      (D : FlatTypeTheory.derivation T H J)
    : FlatTypeTheory.derivation
        (FlatTypeTheory.fmap f T)
        (Family.fmap (fmap_judgement_total f) H)
        (fmap_judgement_total f J).
  Proof.
    refine (Closure.fmap_derivation_over _ D).
    apply FlatTypeTheory.fmap_closure_system.
    apply flat_type_theory_map_to_fmap.
  Defined.
  
  (* TODO: upstream! and check if duplicate? *)
  Local Definition closure_derivation_fmap_hyps
      {X} {T : Closure.system X} {H H'} (f : Family.map H H') {x}
      (D : Closure.derivation T H x)
    : Closure.derivation T H' x.
  Proof.
    refine (Closure.graft _ D _); intros i.
    apply (Closure.hypothesis' (f i)).
    apply Family.map_commutes.
  Defined.
  
  (* TODO: upstream, as [FlatTypeTheory.fmap_closure_system];
     change existing lemma of that name to [fmap_closure_system_over].
   Also abstract [FlatTypeTheory.map]. *)
  Definition flat_type_theory_fmap_closure_system
      {Σ : signature σ} {T T' : flat_type_theory Σ}
      (f : FlatTypeTheory.map_over (Signature.idmap _) T T')
    : Closure.map (FlatTypeTheory.closure_system T)
                  (FlatTypeTheory.closure_system T').
  Proof.
    refine (transport (fun g => Closure.map_over g _ _) _
             (FlatTypeTheory.fmap_closure_system f)).
    apply path_forall; intros i. apply fmap_judgement_total_idmap.
  Defined.

  (* TODO: upstream *)
  (* TODO: make [Σ] implicit in fields of [flat_rule] *)
  (* TODO: rename [flat_rule_premises] to [flat_rule_premise] *)
  Lemma flat_rule_eq
      {Σ : signature σ} {R R' : flat_rule Σ}
      (e_metas : flat_rule_metas _ R = flat_rule_metas _ R')
      (e_premises
       : transport (fun a => family (_ (_ _ a))) e_metas
                   (flat_rule_premises _ R)
         = flat_rule_premises _ R')
      (e_conclusion
       : transport (fun a => judgement_total (_ _ a)) e_metas
                   (flat_rule_conclusion _ R)
         = flat_rule_conclusion _ R')
    : R = R'.
  Proof.
    destruct R, R'; cbn in *.
    destruct e_metas, e_premises, e_conclusion.
    apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma family_fmap_idmap
      {X} (K : family X)
    : Family.fmap idmap K = K.
  Proof.
    apply idpath.
  Defined.

  (* TODO: upstream *)
  Lemma flat_rule_fmap_idmap
      {Σ : signature σ} (R : flat_rule Σ)
    : FlatRule.fmap (Signature.idmap _) R = R.
  Proof.
    simple refine (flat_rule_eq _ _ _).
    - apply idpath.
    - cbn.
      eapply concat.
      { refine (ap (fun f => Family.fmap f _) _).
        eapply concat. { apply ap, Metavariable.fmap1_idmap. }
        apply path_forall; intros i.
        apply Judgement.fmap_judgement_total_idmap. }
      apply family_fmap_idmap.
    - cbn.
      eapply concat. 2: { apply fmap_judgement_total_idmap. }
      apply ap10, ap. apply Metavariable.fmap1_idmap.
  Defined.

  (* TODO: upstream *)
  Lemma flat_rule_fmap_compose
      {Σ Σ' Σ'' : signature σ}
      (f : Signature.map Σ Σ') (f' : Signature.map Σ' Σ'')
      (R : flat_rule Σ)
    : FlatRule.fmap (Signature.compose f' f) R
      = FlatRule.fmap f' (FlatRule.fmap f R).
  Proof.
    simple refine (flat_rule_eq _ _ _).
    - apply idpath.
    - cbn.
      eapply concat. 2: { apply Family.fmap_comp. }
      refine (ap (fun f => Family.fmap f _) _).
      eapply concat. { apply ap, Metavariable.fmap1_compose. }
    (* TODO: rename [Family.fmap_comp] to [Family.fmap_compose], for consistency *)
      apply path_forall; intros i.
      apply Judgement.fmap_judgement_total_compose.
    (* TODO: [Judgement.fmap_judgement_total_compose] shouldn’t be local! *)
    - cbn.
      eapply concat. 2: { apply Judgement.fmap_judgement_total_compose. }
      apply ap10, ap, Metavariable.fmap1_compose.
  Defined.

  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {hjf_concl} {R : rule Σ a hjf_concl}
      {T} (D : is_well_typed T R)
    : is_well_typed (FlatTypeTheory.fmap f T) (RawRule.fmap f R).
  Proof.
    split.
    - (* premises *)
      (* should go via a lemma [AlgebraicExtension.fmap], which should be
         similar to the conclusion case here but with a little extra work
         to deal with the ordering on premises *)
      admit.
    - (* conclusion *)
      set (fR_concl := RawRule.conclusion_boundary (RawRule.fmap f R)).
      assert (e_concl : fR_concl = fmap_judgement_boundary
                               (Metavariable.fmap1 f _)
                               (RawRule.conclusion_boundary R)). 
        { admit. } (* TODO: lemma for this. *)
      clearbody fR_concl. destruct e_concl^.
      intros i.
      set (Di := (snd D) (presupposition_fmap_judgement_boundary _ _ i)).
      (* [Di] is essentially what we want, modulo some translation. *)
      refine (transport _
        (Family.map_commutes (presupposition_fmap_judgement_boundary _ _) i) _).
      match goal with
      | [|- FlatTypeTheory.derivation _ _ ?JJ ] => set (J := (JJ)) in *
      | _ => fail
      end.
      unfold Family.fmap, family_element in J.
      subst J.
      assert (fDi := flat_type_theory_fmap_derivation (Metavariable.fmap1 f a) Di).
      clear D Di e_concl. (* just tidying up *)
      refine (Closure.fmap_derivation _ (closure_derivation_fmap_hyps _ fDi)).
      + (* commutativity in type theory *)
        apply flat_type_theory_fmap_closure_system.
        apply flat_type_theory_map_from_family_map.
        (* TODO: abstract the follwing as lemma? *)
        exists idmap.
        intros r; simpl.
        eapply concat. { apply inverse, flat_rule_fmap_compose. }
        eapply concat. 2: { apply inverse, flat_rule_fmap_idmap. }
        eapply concat. 2: { apply flat_rule_fmap_compose. }
        apply ap10, ap.
        (* TODO: lemma about naturality of [include_symbol]. *)
        admit.
      + (* commutativity in hypotheses *)
        cbn. exists idmap.
        admit. (* TODO: lemma for this, together with [e_concl] above. *) 
  Admitted.

End Functoriality.

Section Flattening.

  Context {σ : shape_system} `{Funext}.

  Definition weakly_well_typed_flatten
      {Σ : signature σ} {T : flat_type_theory Σ}
      {a} {hjf_concl}
      {R : rule Σ a hjf_concl}
      (T_WT : is_well_typed T R)
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
          (flat_rule_conclusion _ (RawRule.flatten R Sr))).
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