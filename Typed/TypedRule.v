Require Import HoTT.
Require Import Proto.ShapeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Raw.AlgebraicExtension.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.
Require Import Raw.RawRule.
Require Import Raw.RawTypeTheory.
Require Import Raw.CongruenceRule.
Require Import Typed.TypedFlatRule.

(** In this file: definition of well-typedness of an algebraic extension, and a (well-presented) rule. *)

Section WellTypedRule.

  Context {σ : shape_system}.

  (* TODO: upstream to new file [TypedAlgebraicExtension]. *)
  Definition is_well_typed_algebraic_extension
      {Σ : signature σ} (T : flat_type_theory Σ)
      {a} (A : algebraic_extension Σ a)
    : Type.
  Proof.
    refine (forall r : A, _).
    exact (forall
     (i : presupposition_of_boundary (AlgebraicExtension.premise_boundary r)),
      FlatTypeTheory.derivation
        (FlatTypeTheory.fmap include_symbol T)
        (AlgebraicExtension.flatten (AlgebraicExtension.initial_segment A r))
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

  (* TODO: consider naming.  Currently a bit out of step with our general convention of using e.g. [derivation] not [is_derivable]; but [derivation] would be misleading here, since this is the type of derivations showing that the rule is well-formed, not “derivations of the rule” in the usual sense of derivations showing it’s a derivable rule. *) 
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

  Context {σ : shape_system} `{Funext}.

  Definition fmap_is_well_typed_algebraic_extension
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {A : algebraic_extension Σ a}
      {T} (D : is_well_typed_algebraic_extension T A)
    : is_well_typed_algebraic_extension
        (FlatTypeTheory.fmap f T) (AlgebraicExtension.fmap f A).
  Proof.
    unfold is_well_typed_algebraic_extension.
    intros p.
    change (AlgebraicExtension.premise_boundary p)
    with (Judgement.fmap_boundary
            (Metavariable.fmap1 f _)
            (@AlgebraicExtension.premise_boundary _ _ _ A p)). 
    intros i.
    set (Di := D p (Judgement.presupposition_fmap_boundary _ _ i)).
    (* [Di] is essentially what we want, modulo some translation. *)
    refine (transport _
      (Family.map_commutes (Judgement.presupposition_fmap_boundary _ _) i) _).
    match goal with
    | [|- FlatTypeTheory.derivation _ _ ?JJ ] => set (J := (JJ)) in *
    | _ => fail
    end.
    unfold Family.fmap, family_element in J.
    subst J.
    assert (fDi :=
      FlatTypeTheory.fmap_derivation (Metavariable.fmap1 f _) Di).
    clear D Di. (* just tidying up *)
    refine (FlatTypeTheory.fmap_derivation_in_theory _ (Closure.derivation_fmap2 _ fDi)).
      + (* commutativity in type theory *)
        apply FlatTypeTheory.map_from_family_map.
        (* TODO: abstract the follwing as lemma? *)
        exists idmap.
        intros r; simpl.
        eapply concat. { apply inverse, FlatRule.fmap_compose. }
        eapply concat. 2: { apply FlatRule.fmap_compose. }
        apply ap10, ap.
        apply Metavariable.include_symbol_after_map.
      + (* commutativity in hypotheses *)
        cbn. exists idmap; intros j.
        eapply concat. 2: { apply AlgebraicExtension.flatten_fmap. }
        apply AlgebraicExtension.flatten_initial_segment_fmap_applied.
  Defined.

  (** Well-typedness is _covariant_ in the signature *)
  Local Definition fmap_is_well_typed
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {hjf_concl} {R : rule Σ a hjf_concl}
      {T} (D : is_well_typed T R)
    : is_well_typed (FlatTypeTheory.fmap f T) (RawRule.fmap f R).
  Proof.
    split.
    (* premises *)
    { apply fmap_is_well_typed_algebraic_extension, (fst D). }
    (* conclusion *)
    set (fR_concl := RawRule.conclusion_boundary (RawRule.fmap f R)).
    assert (e_concl : fR_concl = Judgement.fmap_boundary
                             (Metavariable.fmap1 f _)
                             (RawRule.conclusion_boundary R)). 
      { apply RawRule.conclusion_boundary_fmap. }
    clearbody fR_concl. destruct e_concl^.
    intros i.
    set (Di := (snd D) (Judgement.presupposition_fmap_boundary _ _ i)).
    (* [Di] is essentially what we want, modulo some translation. *)
    refine (transport _
      (Family.map_commutes (Judgement.presupposition_fmap_boundary _ _) i) _).
    match goal with
    | [|- FlatTypeTheory.derivation _ _ ?JJ ] => set (J := (JJ)) in *
    | _ => fail
    end.
    unfold Family.fmap, family_element in J.
    subst J.
    assert (fDi :=
      FlatTypeTheory.fmap_derivation (Metavariable.fmap1 f a) Di).
    clear D Di e_concl. (* just tidying up *)
    refine (FlatTypeTheory.fmap_derivation_in_theory _ (Closure.derivation_fmap2 _ fDi)).
    - (* commutativity in type theory *)
      apply FlatTypeTheory.map_from_family_map.
      (* TODO: abstract the follwing as lemma? *)
      exists idmap.
      intros r; simpl.
      eapply concat. { apply inverse, FlatRule.fmap_compose. }
      eapply concat. 2: { apply FlatRule.fmap_compose. }
      apply ap10, ap.
      apply Metavariable.include_symbol_after_map.
    - (* commutativity in hypotheses *)
      cbn. exists idmap.
      apply AlgebraicExtension.flatten_fmap.
  Defined.

  (** Well-typedness is _contravariantly_ functorial in the ambient theory. *)
  (* TODO: consider naming! *)
  Definition fmap_is_well_typed_algebraic_extension_in_theory {Σ : signature σ}
      {T T' : flat_type_theory Σ} (f : FlatTypeTheory.map T T')
      {a} {A : algebraic_extension Σ a}
    : is_well_typed_algebraic_extension T A
      -> is_well_typed_algebraic_extension T' A.
  Proof.
    intros A_WT r p.
    refine (FlatTypeTheory.fmap_derivation_in_theory _ (A_WT r p)).
    apply FlatTypeTheory.fmap_map, f.
  Defined.

  (** Well-typedness is _contravariantly_ functorial in the ambient theory. *)
  (* TODO: consider naming! *)
  Definition fmap_is_well_typed_in_theory {Σ : signature σ}
      {T T' : flat_type_theory Σ} (f : FlatTypeTheory.map T T')
      {a} {hjf_concl} {R : rule Σ a hjf_concl}
    : is_well_typed T R -> is_well_typed T' R.
  Proof.
    intros R_WT.
    split. { exact (fmap_is_well_typed_algebraic_extension_in_theory f (fst R_WT)). }
    intros p.
    refine (FlatTypeTheory.fmap_derivation_in_theory _ (snd R_WT p)).
    apply FlatTypeTheory.fmap_map, f.
  Defined.

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
          (flat_rule_conclusion (RawRule.flatten R Sr))).
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

Section Congruence_Rules.

  Context {σ : shape_system} `{Funext}.

  Definition congruence_rule_is_well_typed
      {Σ : signature σ} {T : flat_type_theory Σ}
      {a} {hjf_concl} {R : rule Σ a hjf_concl} (R_WT : is_well_typed T R)
      (R_is_ob : Judgement.is_object hjf_concl)
      (S : Σ)
      (e_a : symbol_arity S = a)
      (e_cl : symbol_class S = Judgement.class_of hjf_concl)
    : is_well_typed T (congruence_rule R R_is_ob S e_a e_cl).
  Proof.
  Admitted. (* [congruence_rule_is_well_typed]: large, key stress test of functoriality framework for derivability *)

End Congruence_Rules.