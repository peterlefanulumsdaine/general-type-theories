Require Import HoTT.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.Family.
Require Import Auxiliary.WellFounded.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Presented.AlgebraicExtension.
Require Import Typing.FlatRule.
Require Import Typing.FlatTypeTheory.
Require Import Presented.RawRule.
Require Import Presented.RawTypeTheory.
Require Import Presented.CongruenceRule.
Require Import Typing.Presuppositions.

(** In this file: definition of well-typedness of an algebraic extension, and a (well-presented) rule. *)

Section WellTypedRule.

  Context {σ : scope_system}.

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
      {a} {jf_concl}
      (R : rule Σ a jf_concl)
    : Type.
  Proof.
    refine (is_well_typed_algebraic_extension T (rule_premise R) * _).
    (* well-typedness of conclusion *)
    exact
      (forall (i : presupposition_of_boundary (RawRule.conclusion_boundary R)),
        FlatTypeTheory.derivation
          (FlatTypeTheory.fmap include_symbol T)
          (AlgebraicExtension.flatten (rule_premise R))
          (presupposition_of_boundary _ i)).
  Defined.

End WellTypedRule.

Section Functoriality.

  Context {σ : scope_system} `{Funext}.

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
    set (Di := D p (presupposition_fmap_boundary _ _ i)).
    (* [Di] is essentially what we want, modulo some translation. *)
    refine (transport _
      (Family.map_commutes (presupposition_fmap_boundary _ _) i) _).
    match goal with
    | [|- FlatTypeTheory.derivation _ _ ?JJ ] => set (J := (JJ)) in *
    | _ => fail
    end.
    unfold Family.fmap, family_element in J.
    subst J.
    refine (FlatTypeTheory.derivation_fmap_over_simple _ _ _ Di).
    - (* map in type theory *)
      (* TODO: refactor to be higher-level, eg using [FlatTypeTheory.fmap_compose]? *)
      exists idmap.
      intros r; simpl.
      eapply concat. { apply inverse, FlatRule.fmap_compose. }
      eapply concat. 2: { apply FlatRule.fmap_compose. }
      apply ap10, ap.
      apply Metavariable.include_symbol_after_map.
    - (* map in hypotheses *)
      cbn. exists idmap; intros j.
      eapply concat. 2: { apply AlgebraicExtension.flatten_fmap. }
      apply AlgebraicExtension.flatten_initial_segment_fmap_applied.
  Defined.

  (** Well-typedness is _covariant_ in the signature *)
  Local Definition fmap_is_well_typed
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {a} {jf_concl} {R : rule Σ a jf_concl}
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
    set (Di := (snd D) (presupposition_fmap_boundary _ _ i)).
    (* [Di] is essentially what we want, modulo some translation. *)
    refine (transport _
      (Family.map_commutes (presupposition_fmap_boundary _ _) i) _).
    match goal with
    | [|- FlatTypeTheory.derivation _ _ ?JJ ] => set (J := (JJ)) in *
    | _ => fail
    end.
    unfold Family.fmap, family_element in J.
    subst J.
    refine (FlatTypeTheory.derivation_fmap_over_simple _ _ _ Di).
    - (* map in type theory *)
      (* TODO: refactor using [FlatTypeTheory.fmap_compose]? *)
      exists idmap.
      intros r; simpl.
      eapply concat. { apply inverse, FlatRule.fmap_compose. }
      eapply concat. 2: { apply FlatRule.fmap_compose. }
      apply ap10, ap.
      apply Metavariable.include_symbol_after_map.
    - (* map in hypotheses *)
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
    refine (FlatTypeTheory.derivation_fmap1 _ (A_WT r p)).
    apply FlatTypeTheory.map_fmap, f.
  Defined.

  (** Well-typedness is _contravariantly_ functorial in the ambient theory. *)
  (* TODO: consider naming! *)
  Definition fmap_is_well_typed_in_theory {Σ : signature σ}
      {T T' : flat_type_theory Σ} (f : FlatTypeTheory.map T T')
      {a} {jf_concl} {R : rule Σ a jf_concl}
    : is_well_typed T R -> is_well_typed T' R.
  Proof.
    intros R_WT.
    split.
    { exact (fmap_is_well_typed_algebraic_extension_in_theory f (fst R_WT)). }
    intros p.
    refine (FlatTypeTheory.derivation_fmap1 _ (snd R_WT p)).
    apply FlatTypeTheory.map_fmap, f.
  Defined.

End Functoriality.

Section Flattening.

  Context {σ : scope_system} `{Funext}.

  Definition weakly_presuppositive_flatten
      {Σ : signature σ} {T : flat_type_theory Σ}
      {a} {jf_concl}
      {R : rule Σ a jf_concl}
      (T_WT : is_well_typed T R)
      (Sr : Judgement.is_object jf_concl ->
        {S : Σ.(family_index) &
        (symbol_arity S = a) * (symbol_class S = Judgement.class_of jf_concl)})
    : weakly_presuppositive_flat_rule T (RawRule.flatten R Sr).
  Proof.
    apply snd in T_WT.
    intros i.
    refine (Closure.graft' (T_WT i) _ _).
    - recursive_destruct jf_concl; apply idpath.
    - clear i. intros i.
      exact (Closure.hypothesis _ (_+_) (inl i)).
  Qed.
  (* NOTE: in fact, we should be able to extend this to showing
   that [flatten R] is _strongly_ presuppositive. *)

End Flattening.

Section Congruence_Rules.

  Context {σ : scope_system} `{Funext}.

  Definition congruence_rule_is_well_typed
      {Σ : signature σ} {T : flat_type_theory Σ}
      {a} {jf_concl} {R : rule Σ a jf_concl} (R_WT : is_well_typed T R)
      (R_is_ob : Judgement.is_object jf_concl)
      (S : Σ)
      (e_a : symbol_arity S = a)
      (e_cl : symbol_class S = Judgement.class_of jf_concl)
    : is_well_typed T (congruence_rule R R_is_ob S e_a e_cl).
  Proof.
  Admitted. (* [congruence_rule_is_well_typed]: large, key stress test of functoriality framework for derivability *)

End Congruence_Rules.
