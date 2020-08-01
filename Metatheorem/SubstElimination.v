Require Import HoTT.
Require Import Syntax.ScopeSystem.
Require Import Auxiliary.General.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Auxiliary.Coproduct.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.StructuralRule.
Require Import Typing.FlatTypeTheory.

(** The main goal of this file is the theorem [subst_elimination], showing
that for suitable theories [T], any derivation over [T] using the full
structural rules can be translated into a derivation not using the rules
[subst_apply], [subst_equal].

The main subsidiary lemmas are [subst_apply_admissible] and
[subst_equal_admissible], showing that (generalisations of) these rules are
admissible over the closure system given by [T] together with the other
structural rules.

Note: at the moment, our “susbt-free” structural rules still include the
general renaming rule.  In fact the subst-free derivations we produce will
only require renaming along _equivalences_ of scopes. *)

(* TODO: perhaps restrict the renaming rule (either in general, or just
in [structural_rule_without_subst]) to just the case of equivalences,
so that the results of this file really do show that general renaming is
admissible. *)

Section Subst_Free_Derivations.

  Context {σ : scope_system}.

  Definition closure_system_without_subst
      {Σ : signature σ} (T : flat_type_theory Σ)
  := structural_rule_without_subst Σ + Family.bind T FlatRule.closure_system.

  Definition subst_free_derivation
      {Σ : signature σ} (T : flat_type_theory Σ)
  := derivation (closure_system_without_subst T).

  Definition subst_free_rule_derivation {Σ : signature σ}
    (T : flat_type_theory Σ) (R : flat_rule Σ)
  := subst_free_derivation
      (FlatTypeTheory.fmap Metavariable.include_symbol T)
      (flat_rule_premise R)
      (flat_rule_conclusion R).

End Subst_Free_Derivations.

Section Flat_Conditions.
(** Conditions on flat rules/type theories sufficient for admissibility of
substitution to hold over them.

  The main such condition is: every rule should have empty conclusion context.
To use one established terminology, all rules should be in _universal form_,
as opposed to _hypothetical form_.

  For substitution to (admissibly) respect equality, we additionally need to
know that the theory is _congruous_, in that for each flat rule of object form,
the associated congruence rule should be derivable (?admissible). *)

  Context {σ} {Σ : signature σ}.

  Definition in_universal_form (R : flat_rule Σ)
    := is_empty (scope_of_judgement (flat_rule_conclusion R)).

  Definition substitutive (T : flat_type_theory Σ)
    := forall r : T, in_universal_form (T r).

  Local Definition congruous (T : flat_type_theory Σ)
    : Type
  := Family.map
    (Family.bind T
       (fun R => {| family_element R_obj := flat_congruence_rule R R_obj |}))
    T.
  (** More readably: [T] is congruous if for each of its object rules, it also contains the associated congruence rule.

  This is not as general as would ideally be nice: ideally we would say something like “for each object rule, the associated congruence rule is _derivable_ over T”. Unfortunately, the obvious concise ways of saying that all seem to be wrong.

  For instance, our main sense of derivable says that the rule itself is derivable over the translation of T to the metavariable extension; this is bad for two reasons.  First, applying this notion relies on being able to instantiate derivations, which requires either the subst-apply rule or a subst-elimination principle, which will not yet be available at the point we need this.  Secondly, in examples, giving derivations with non-trivial hypotheses (as one does for a congruence rule with binders) may genuinely require use of the subst-apply and subst-eq structural rules.

  An alternative would be to just say that the congruence rule should be _admissible_ over T, or that each instance of it should be derivable.  These would work for the present theorems, but are a bit unnatural; e.g. they’re not preserved under translation or extension of theories.

  The best notion is perhaps obtained by re-defining “derivable rule” to fit the subst-free setting.  For this, we say “the rule’s conclusion should be derivable in the metavariable extension” as before, but instead of saying “…over T, from the rule’s premises”, we convert the premises into extra rules; a premise like [ x:A |- B(x) type ] becomes a pair of rules
[ |- a:A // |- B(a) type ] and [ |- a = a' : A // |- B(a) = B(a') type ].

  With “derivable rule” thus re-defined, taking “congruous” to be “each associated congruence rule is derivable over T” should now work well: it should suffice for the theorems of this file, and be applicable to natural examples (i.e. theories set up using alternative resonable formulations of congruence rules). More generally, this seems to be the right notion of “derivable rule” in the subst-free setting, so would be good to have in general.

  However, it would take a lot of work to state this and set up the infrastructure to work with it.  So for now we stick with this simpler and cruder notion of congruousness: T should literally contain all its associated congruence rules. *)

  (* TODO: this could be improved in several ways, given a bit of upstream refactoring:
  - factor the definition of [FlatTypeTheory.closure_system] and the [without subst] version to have the second summand defined together, then have this hold for any closure system with a map from that
  - then can upstream this to [FlatTypeTheory] (along with following couple of rules)
  - also can possibly add “contains” relation for families, then rewrite this to use that *)
  Local Definition derive_contained_rule
      {T : flat_type_theory Σ}
      {R} {r:T} (e : T r = R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {H} (d_prems : forall p : flat_rule_premise R,
             subst_free_derivation T H
                        (Judgement.instantiate Γ I (flat_rule_premise R p)))
    : subst_free_derivation T H
        (Judgement.instantiate Γ I (flat_rule_conclusion R)).
  Proof.
    destruct e.
    simple refine (Closure.deduce' _ _ _).
    { apply inr. exists r, Γ. exact I. }
    { apply idpath. }
    assumption.
  Defined.

  (* TODO: as with [derive_contained_rule], upstream once refactored to allow that *)
  Local Definition derive_contained_rule'
      {T : flat_type_theory Σ}
      {R} {r:T} (e_R : T r = R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J} (e_J : J = Judgement.instantiate Γ I (flat_rule_conclusion R))
      {H} (d_prems : forall p : flat_rule_premise R,
             subst_free_derivation T H
                        (Judgement.instantiate Γ I (flat_rule_premise R p)))
    : subst_free_derivation T H J.
  Proof.
    destruct e_J^; eapply derive_contained_rule; eassumption.
  Defined.

  Local Definition derive_congruence {T} (T_cong : congruous T) {H}
    {r : T} (r_obj : Judgement.is_object (form_of_judgement (flat_rule_conclusion (T r))))
    (r_cong := flat_congruence_rule (T r) r_obj)
    {Γ : raw_context Σ}
    (I0 I1 : Metavariable.instantiation (flat_rule_metas (T r)) Σ Γ)
    (I := copair_instantiation I0 I1)
    (d_prems : forall p : flat_rule_premise r_cong,
        subst_free_derivation T H
          (Judgement.instantiate Γ I (flat_rule_premise r_cong p)))
    : subst_free_derivation T H
        (Judgement.instantiate Γ I (flat_rule_conclusion r_cong)).
  Proof.
    simple refine (derive_contained_rule _ _ _).
    { apply T_cong. exists r. exact r_obj. }
    { apply (Family.map_commutes T_cong). }
    assumption.
  Defined.

  Lemma equality_flat_rules_congruous `{Funext}
      {C} (T := structural_rule_without_subst Σ + C)
      {r : @equality_flat_rule σ}
      (r_obj : Judgement.is_object (form_of_judgement
                               (flat_rule_conclusion (equality_flat_rule r))))
      (r_cong := flat_congruence_rule
         (FlatRule.fmap (Signature.empty_rect Σ) (equality_flat_rule r)) r_obj)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas r_cong) Σ Γ)
    : derivation T
        (Family.fmap (Judgement.instantiate Γ I) (flat_rule_premise r_cong))
        (Judgement.instantiate Γ I (flat_rule_conclusion r_cong)).
  Proof.
    recursive_destruct r; destruct r_obj.
    (* Only one equality rule is an object rule: [term_convert].  Its congruence rule is essentially:
  [! Γ |- A !] [! Γ |- A' !] [! Γ |- A ≡ A' !]
  [! Γ |- B !] [! Γ |- B' !] [! Γ |- B ≡ B' !]
  [! Γ |- A ≡ B !] [! Γ |- A' ≡ B' !]
  [! Γ |- u ; A !] [! Γ |- u' ; A' !] [! Γ |- u ≡ u' ; A !]
---------------------------------------------------------------
  [! Γ |- u = u' ; B !]

This is derived quite easily, using [tmeq_convert], [term_convert], and [tyeq_sym].

The below proof follows that derivation directly, but giving it is a bit like playing blindfold chess: the bureaucracy of instantiations, reindexings, etc. makes the actual expression/judgements involved mostly unreadable. *)
    apply Judgement.canonicalise; simpl Judgement.eta_expand.
    eapply derive_tmeq_convert.
    - (* [! Γ |- A !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inl, inl, Some, Some, Some, tt. }
      apply Judgement.eq_by_eta, idpath.
    - (* [! Γ |- B !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inl, inl, Some, Some, None. }
      apply Judgement.eq_by_eta, idpath.
    - (* [! Γ |- A ≡ B !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inl, inl, Some, None. }
      apply Judgement.eq_by_eta, idpath.
    - (* [! Γ |- u ; A !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inl, inl, None. }
      apply Judgement.eq_by_eta, idpath.
    - (* [! Γ |- u' ; A !] *)
      eapply derive_term_convert.
      + (* [! Γ |- A' !] *)
        simple refine (Closure.hypothesis' _ _).
        { apply inl, inr, Some, Some, Some, tt. }
        refine (Judgement.eq_by_expressions _ _).
        * apply (coproduct_rect scope_is_sum).
          -- intro i.
             repeat rewrite coproduct_comp_inj1; apply idpath.
          -- apply (empty_rect _ scope_is_empty).
        * intro s; recursive_destruct s; apply idpath.
      + (* [! Γ |- A !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inl, inl, Some, Some, Some, tt. }
      apply Judgement.eq_by_eta, idpath.
      + (* [! Γ |- A' ≡ A !] *)
        apply derive_tyeq_sym.
        simple refine (Closure.hypothesis' _ _).
        { apply inr. exists (Some (Some (Some tt))). exact tt. }
        apply Judgement.eq_by_eta, idpath.
      + (* [! Γ |- u' ; A' !] *)
        simple refine (Closure.hypothesis' _ _).
        { apply inl, inr, None. }
        refine (Judgement.eq_by_expressions _ _).
        * apply (coproduct_rect scope_is_sum).
          -- intro i.
             repeat rewrite coproduct_comp_inj1; apply idpath.
          -- apply (empty_rect _ scope_is_empty).
        * intro s; recursive_destruct s; apply idpath.
    - (* [! Γ |- u ≡ u' ; A !] *)
      simple refine (Closure.hypothesis' _ _).
      { apply inr. exists None. exact tt. }
      apply Judgement.eq_by_eta, idpath.
  Time Defined.
  (* TODO: trying to bring this timing down seems like a good test case for improving our derivation infrastructure. *)

End Flat_Conditions.

Section Judgement_Renamings.
(** A lot of results can be concisely formulated in terms of maps/renamings of
judgements.  A map/renaming of judgements from [Γ' |- J'] to [Γ |- J] is just
a context map/renaming [f] from [Γ'] to [J], such that [J' = f^*J].

(Categorically, these are exactly maps in the total category of judgements,
viewed as a discrete fibration over contexts.)

This section gives judgement renamings; section [Weakly_Typed_Maps] below gives
the analogue for (weakly) typed context maps. *)

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  (* TODO: perhaps upstream judgement renamings to [Judgement.v], and use them
  more widely, e.g. in the renaming structural rules?? *)

  Record judgement_renaming (J J' : judgement Σ)
  := {
    typed_renaming_of_judgement_renaming
      :> typed_renaming (context_of_judgement J) (context_of_judgement J')
  ; judgement_renaming_hypothetical_part
      : rename_hypothetical_judgement
          typed_renaming_of_judgement_renaming
          (hypothetical_part J)
        = hypothetical_part J'
  }.

  Lemma judgement_renaming_inverse
      (J J' : judgement Σ)
      (f : judgement_renaming J J')
      (e_f : IsEquiv f)
    : judgement_renaming J' J.
  Proof.
    exists (typed_renaming_inverse _ e_f).
    eapply concat.
    { apply ap, inverse, (judgement_renaming_hypothetical_part _ _ f). }
    eapply concat. { apply rename_rename_hypothetical_judgement. }
    eapply concat. 2: { apply rename_idmap_hypothetical_judgement. }
    apply (ap_1back rename_hypothetical_judgement), path_forall; intros i.
    apply eissect.
  Defined.

  Lemma instantiate_judgement_over_typed_renaming
      {Γ Γ' : raw_context Σ} (f : typed_renaming Γ Γ')
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : judgement_renaming
        (Judgement.instantiate Γ I J)
        (Judgement.instantiate Γ' (rename_instantiation f I) J).
  Proof.
    exists (instantiate_context_over_typed_renaming f I _).
    apply inverse, instantiate_hypothetical_judgement_rename_instantiation.
  Defined.

End Judgement_Renamings.

Section Rename_Derivations.
(** The goal of this section is [rename_derivation]:
given a judgement-renaming from [J] to [J'],
and a derivation [d] of [J],
we can rename throughout [d] to get a derivation of [J'].

The proof of [rename_derivation] is by direct structural induction on
derivations; the rest of this section is devoted to the lemmas needed in
the cases of that induction. *)

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  Section Flat_Rule_Instantiation_Renaming.
    (** The lemmas of this section build up what’s needed for renaming
     flat-rule steps in derivations:

     given an instance of a flat rule in universal form,
     and a judgement-renaming into its conclusion,
     get a renamed instance, whose conclusion is renaming-equivalent to the
     renaming we want to derive, and each of whose premises has a
     judgement-renaming to some premise of the original rule.

     The cases for non-flat structural rules are done by analogous
     claim for their closure conditions.
    *)

    (* TODO: consider naming of the whole following lemma sequence *)

    Context {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J' : judgement Σ}
      (f : judgement_renaming
             (Judgement.instantiate Γ I (flat_rule_conclusion R))
             J')
      (Γ' := context_of_judgement J').

    Local Definition rename_flat_rule_instantiation_renaming
      : typed_renaming Γ Γ'.
    Proof.
      refine (compose_typed_renaming f _).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition rename_flat_rule_instantiation_instantiation
      : Metavariable.instantiation (flat_rule_metas R) Σ Γ'.
    Proof.
      exact (rename_instantiation
               rename_flat_rule_instantiation_renaming
               I).
    Defined.

    Local Lemma rename_flat_rule_instantiation_conclusion
      : judgement_renaming
          (Judgement.instantiate Γ'
            (rename_flat_rule_instantiation_instantiation)
            (flat_rule_conclusion R))
          J'.
    (* NOTE: and moreover this judgement_renaming is an equivalence, which may
    be needed if we restrict the renaming structural rule to equivalences. *)
    Proof.
      simple refine (judgement_renaming_inverse _ _ _ _).
      1: exists (typed_renaming_to_instantiate_context _ _ _).
      2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
      eapply concat. 2: { apply inverse,
                      instantiate_hypothetical_judgement_rename_instantiation. }
      eapply concat.
        { apply ap, inverse, (judgement_renaming_hypothetical_part _ _ f). }
      eapply concat. { apply rename_rename_hypothetical_judgement. }
      apply (ap_1back rename_hypothetical_judgement), path_forall.
      refine (coproduct_rect scope_is_sum _ _ _).
      2: { refine (empty_rect _ _ _). apply R_univ. }
      intros x1.
      unfold Coproduct.fmap. repeat rewrite coproduct_comp_inj1.
      apply idpath.
      (* This can be seen more conceptually as a sort of naturality calculation,
       involving naturality of [typed_renaming_to_instantiate_context] w.r.t.
       [instantiate_context_over_typed_renaming]. *)
    Defined.

    Local Lemma rename_flat_rule_instantiation_premise
          (p : flat_rule_premise R)
      : judgement_renaming
          (Judgement.instantiate Γ I (flat_rule_premise R p))
          (Judgement.instantiate Γ' rename_flat_rule_instantiation_instantiation
                                                       (flat_rule_premise R p)).
    Proof.
      apply instantiate_judgement_over_typed_renaming.
    Defined.

  End Flat_Rule_Instantiation_Renaming.

  Lemma equality_flat_rules_in_universal_form
    : forall r : @equality_flat_rule σ,
      in_universal_form (equality_flat_rule r).
  Proof.
    intro r; recursive_destruct r; apply scope_is_empty.
  Defined.

  (** \cref{thm:admissibility-renaming} *)
  Definition rename_derivation
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {J} {J'} (f : judgement_renaming J J')
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    revert J' f.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' f.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (rename_flat_rule_instantiation_conclusion _ _ f)
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inr. exists r.
        exists (context_of_judgement J').
        refine (rename_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ f p).
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (rename_flat_rule_instantiation_conclusion _ _ f)
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inr. exists r.
        exists (context_of_judgement J').
        refine (rename_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ f p).
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_typed_renaming f g).
      eapply concat. 2: { apply (judgement_renaming_hypothetical_part _ _ f). }
      apply inverse, @rename_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in f.
      destruct J' as [Γ' J'].
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inl, inr.
        exists Γ'. exact (f i). }
      { cbn. apply ap.
        set (e := judgement_renaming_hypothetical_part _ _ f).
        eapply concat. 2: { apply e. }
        apply eq_by_expressions_hypothetical_judgement; intros s.
        recursive_destruct s; try apply idpath.
        apply typed_renaming_respects_types.
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := typed_renaming_of_judgement_renaming _ _ f).
      cbn in f0. exists f0.
      apply eq_by_expressions_hypothetical_judgement; intros s.
      recursive_destruct s.
      apply inverse, typed_renaming_respects_types.
  Defined.

End Rename_Derivations.

Section Weakly_Typed_Maps.
(** For [sustitute_derivation], we introduce an auxiliary notion of _weakly
typed_ context maps: maps which at each component look either like a well-typed
context map, or like a typed renaming.

This slightly subtle definition is essentially motivated by the proof
of [substitute_derivation], and in particular, the desire to keep that proof
structurally recursive on the derivation (and also not dependent on any kind
of well-typedness conditions on the flat rules).  The point is that when
passing under binders in premises of rules, we want to extend the context map
by the type-expressions of the binders, without having to check that these are
well-formed. *)

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  Local Definition weakly_typed
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ) (f : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j) * (Δ j = substitute f (Γ i)) }
    + subst_free_derivation T (Family.empty _)
                            [! Δ |- f i ; substitute f (Γ i) !].

  Record weakly_typed_context_map
    (T : flat_type_theory Σ) (Δ Γ : raw_context Σ)
  := {
    raw_of_weakly_typed_context_map :> raw_context_map Σ Δ Γ
  ; weakly_typed_context_map_is_weakly_typed
                    : weakly_typed T Δ Γ raw_of_weakly_typed_context_map
  }.

  Local Lemma compose_weakly_typed_context_map_renaming
        {T : flat_type_theory Σ} (T_sub : substitutive T)
        {Γ Γ' Γ'' : raw_context Σ}
        (g : weakly_typed_context_map T Γ' Γ)
        (f : typed_renaming Γ' Γ'')
    : weakly_typed_context_map T Γ'' Γ.
  Proof.
    simple refine (Build_weakly_typed_context_map _ _ _ _ _).
    - intros i. exact (rename f (g i)).
    - intros i.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ g i)
        as [[j [e1 e2]] | d_gi].
      + apply inl.
        exists (f j); split.
        * exact (ap (rename f) e1).
        * eapply concat. { apply typed_renaming_respects_types. }
          eapply concat. { apply ap, e2. }
          apply rename_substitute.
      + apply inr.
        refine (rename_derivation _ _ d_gi).
        { assumption. }
        exists f.
        apply eq_by_expressions_hypothetical_judgement; intros j.
        recursive_destruct j; try apply idpath.
        apply rename_substitute.
  Defined.

  Local Lemma compose_renaming_weakly_typed_context_map
        {T : flat_type_theory Σ}
        {Γ Γ' Γ'' : raw_context Σ}
        (g : typed_renaming Γ Γ')
        (f : weakly_typed_context_map T Γ'' Γ')
    : weakly_typed_context_map T Γ'' Γ.
  Proof.
    simple refine (Build_weakly_typed_context_map _ _ _ _ _).
    - intros i. exact (f (g i)).
    - intros i.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f (g i))
        as [[j [e1 e2]] | d_gi].
      + apply inl.
        exists j; split.
        * exact e1.
        * eapply concat. { exact e2. }
          eapply concat. { apply ap, typed_renaming_respects_types. }
          apply substitute_rename.
      + apply inr.
        refine (transport _ _ d_gi).
        apply (ap (fun A => [! _ |- _ ; A !])).
        eapply concat. { apply ap, typed_renaming_respects_types. }
        apply substitute_rename.
  Defined.

  (* TODO: possible alternate names:
     [instantiate_context_substitute_instantiation],
     [extend_weakly_typed_context_map] *)
  Lemma instantiate_context_over_weakly_typed_context_map
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (f : weakly_typed_context_map T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_typed_context_map T
        (Context.instantiate Γ' (substitute_instantiation f I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    exists (Substitution.extend Γ Γ' Δ f).
    refine (coproduct_rect scope_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
          as [[j [e1 e2]] | d_fi].
      + apply inl.
        exists (coproduct_inj1 scope_is_sum j); split.
        * exact (ap _ e1).
        * rewrite coproduct_comp_inj1.
          eapply concat. { apply ap, e2. }
          eapply concat. { apply rename_substitute. }
          eapply concat. 2: { apply inverse, substitute_rename. }
          apply (ap_2back substitute), path_forall; intros k.
          apply inverse. refine (coproduct_comp_inj1 _).
      + apply inr.
        refine (rename_derivation _ _ d_fi).
        { assumption. }
        exists (typed_renaming_to_instantiate_context _ _ _).
        apply eq_by_expressions_hypothetical_judgement; intros j.
        recursive_destruct j; try apply idpath.
        eapply concat. { apply rename_substitute. }
        eapply concat. 2: { apply inverse, substitute_rename. }
        apply (ap_2back substitute), path_forall; intros j.
        apply inverse. refine (coproduct_comp_inj1 _).
    - intros i. apply inl.
      exists (coproduct_inj2 scope_is_sum i); split.
      + refine (coproduct_comp_inj2 _).
      + cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  (** Analogous to [judgement_renaming] *)
  Record weakly_typed_judgement_map
    (T : flat_type_theory Σ) (J' J : judgement Σ)
  := {
    weakly_typed_context_map_of_judgement_map
      :> weakly_typed_context_map T
           (context_of_judgement J') (context_of_judgement J)
  ; weakly_typed_judgement_map_hypothetical_part
      : substitute_hypothetical_judgement
          weakly_typed_context_map_of_judgement_map
          (hypothetical_part J)
        = hypothetical_part J'
  }.

  Local Lemma instantiate_judgement_over_weakly_typed_context_map
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (f : weakly_typed_context_map T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_typed_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation f I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_typed_context_map T_sub f I _).
    apply inverse, instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

End Weakly_Typed_Maps.

Section Substitute_Derivations.

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  Section Flat_Rule_Substitute_Instantiation.
    (** Analogously to section [Flat_Rule_Susbtitute_Renaming],
     the lemmas of this section build up what’s needed for substituting
     flat-rule steps in derivations:

     given an instance of a flat rule in universal form,
     and a weakly-typed judgement map into its conclusion,
     get a sustituted instance, whose conclusion is renaming-equivalent to the
     renaming we want to derive, and each of whose premises has a
     weakly-typed judgement map to some premise of the original rule.

     The cases for non-flat structural rules should be done by analogous
     claim for their closure conditions.
    *)

    (* TODO: consider naming of the whole following lemma sequence
     (but keep consistent with renaming versions above). *)

    Context
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J' : judgement Σ}
      (f : weakly_typed_judgement_map T
             J'
             (Judgement.instantiate Γ I (flat_rule_conclusion R)))
      (Γ' := context_of_judgement J').

    Local Definition substitute_flat_rule_instantiation_map
      : weakly_typed_context_map T Γ' Γ.
    Proof.
      refine (compose_renaming_weakly_typed_context_map _ f).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition substitute_flat_rule_instantiation_instantiation
      : Metavariable.instantiation (flat_rule_metas R) Σ Γ'.
    Proof.
      exact (substitute_instantiation
               substitute_flat_rule_instantiation_map
               I).
    Defined.

    Local Lemma substitute_flat_rule_instantiation_conclusion
      : judgement_renaming
          (Judgement.instantiate Γ'
            (substitute_flat_rule_instantiation_instantiation)
            (flat_rule_conclusion R))
          J'.
    (* NOTE: and moreover this judgement_renaming is an equivalence, which may
    be needed if we restrict the renaming structural rule to equivalences. *)
    Proof.
      simple refine (judgement_renaming_inverse _ _ _ _).
      1: exists (typed_renaming_to_instantiate_context _ _ _).
      2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
      (* The following can again be seen as a naturality calculation,
       involving naturality of [typed_renaming_to_instantiate_context] w.r.t.
       weakly typed context maps. *)
      eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
      eapply concat.
        { apply ap, inverse, (weakly_typed_judgement_map_hypothetical_part _ _ _ f). }
      eapply concat. { apply rename_substitute_hypothetical_judgement. }
      apply (ap_1back substitute_hypothetical_judgement), path_forall.
      refine (coproduct_rect scope_is_sum _ _ _).
      2: { refine (empty_rect _ _ _). apply R_univ. }
      intros x1.
      unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
      apply idpath.
    Defined.

    Local Lemma substitute_flat_rule_instantiation_premise
          (p : flat_rule_premise R)
      : weakly_typed_judgement_map T
          (Judgement.instantiate Γ'
                  substitute_flat_rule_instantiation_instantiation
                  (flat_rule_premise R p))
          (Judgement.instantiate Γ I (flat_rule_premise R p)).
    Proof.
      apply instantiate_judgement_over_weakly_typed_context_map.
      assumption.
    Defined.

  End Flat_Rule_Substitute_Instantiation.

  (** \cref{lem:substitution-admisibility} *)
  Definition substitute_derivation
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {J} {J'} (f : weakly_typed_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    revert J' f.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' f.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substitute_flat_rule_instantiation_conclusion _ _ f)
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
      assumption.
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substitute_flat_rule_instantiation_conclusion _ _ f)
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
      assumption.
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_renaming_weakly_typed_context_map g f).
      eapply concat.
        2: { apply (weakly_typed_judgement_map_hypothetical_part _ _ _ f). }
      apply inverse, @substitute_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in f.
      destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
        as [[j [e1 e2]] | d_fi].
      (* TODO: add implicit args in […is_weakly_typed]!  It’s bloody long enough already *)
      + (* case: [f i = raw_variable j], [Γ' j = f^* (Γ i) ] *)
      destruct J' as [Γ' J'].
      destruct f as [f fJ'].
      cbn in j, e1, e2 |- *.
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inl, inr. (* use the variable rule *)
        exists Γ'. exact j. }
      { cbn in fJ'; destruct fJ'.
        apply Judgement.eq_by_expressions.
        - intro; apply idpath.
        - intro s; recursive_destruct s.
          + exact e2.
          + cbn. apply inverse, e1.
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := f : weakly_typed_context_map _ _ _).
      cbn in f0. exists f0.
      apply eq_by_expressions_hypothetical_judgement; intros s.
      recursive_destruct s.
      apply inverse, e2.
      + (* case: [f] tells us [ Γ' |- f i : f^* (Γ i) ] *)
        refine (transport _ _ d_fi).
        destruct J' as [Γ' J'].
        destruct f as [f fJ'].
        cbn in fJ' |- *; destruct fJ'.
        apply Judgement.eq_by_eta; exact idpath.
  Defined.

  (** Note: both [rename_derivation] and [sustitute_derivation] have analogues for derivations with hypotheses.  However, these are rather less clear to state, so for now we give just the versions for closed derivations.  *)
End Substitute_Derivations.

Section Equality_Substitution.
(** Goal of this section: showing that (generalisations of) the [subst_equal] structural rules are admissible.

That is: given a derivale object judgement, e.g. [ Γ |- a : A ], and two derivably judgementally equal context morphisms [ f, g : Γ' -> Γ ], we should be able to derive [ Γ |- f^*a = g^*a : f^* A ].

That result, [subst_equal_derivation], is the main goal of this section; but to make the inductive proof go through we generalise its statement, to raw context maps [f g : Γ' -> Γ] that are what we call _weakly judgementally-equal_.

The idea of this is that it generalises judgemental equality so as to be closed under extending a pair [f, g : Δ -> Γ] to extended pairs [Δ;f^*A -> Γ;A] and [Δ;g^*A -> Γ;A], i.e. with the source context extended by either [f^*A] or [g^*A]); and we must do this without any well-formedness check on [A], so we can’t necessarily derive that the extensions are judgementally equal.  Such extensions arise when going under binders in premises of rules.

Since the resulting individual maps [f], [g] may not be weakly-typed context maps, so not automatically applicable for [substitute_derivation], we also strengthen the induction statement to yield additionally that [ Γ |- f^*a : f^*A ] and [ Γ |- g^*a : g^*A ]. *)

  Context {σ : scope_system} {Σ : signature σ} `{Funext}.

  Local Definition weakly_equal
      (T : flat_type_theory Σ)
      {Δ Γ : raw_context Σ}
      (f g : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j)
                * (g i = raw_variable j)
                * ((Δ j = substitute f (Γ i))
                  + (Δ j = substitute g (Γ i))) }
    + subst_free_derivation T (Family.empty _)
          [! Δ |- f i ; substitute f (Γ i) !]
      * subst_free_derivation T (Family.empty _)
          [! Δ |- g i ; substitute g (Γ i) !]
      * subst_free_derivation T (Family.empty _)
          [! Δ |- f i ≡ g i ; substitute f (Γ i) !].

  Record weakly_equal_pair
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ)
  := {
    left : raw_context_map Σ Δ Γ
  ; right : raw_context_map Σ Δ Γ
  ; is_weakly_equal : weakly_equal T left right
  }.

  Arguments Build_weakly_equal_pair {_ _ _} _ _ _.
  Arguments left {_ _ _} _.
  Arguments right {_ _ _} _.
  Arguments is_weakly_equal {_ _ _} _.

  Local Definition compose_renaming_weakly_equal_pair
        {T : flat_type_theory Σ}
        {Γ Γ' Γ'' : raw_context Σ}
        (r : typed_renaming Γ Γ')
        (fg : weakly_equal_pair T Γ'' Γ')
    : weakly_equal_pair T Γ'' Γ.
  Proof.
    set (f := left fg); set (g := right fg).
    simple refine (Build_weakly_equal_pair _ _ _).
    - intros i. exact (f (r i)).
    - intros i. exact (g (r i)).
    - intros i.
      destruct (is_weakly_equal fg (r i))
        as [[j [e1 e2]] | [[d_fri d_gri] d_fgri] ].
      + apply inl.
        exists j; split.
        * exact e1.
        * destruct e2 as [e2|e2] ; [apply inl | apply inr];
            refine (e2 @ _);
            refine (ap _ _ @ _);
            try apply typed_renaming_respects_types;
            apply substitute_rename.
      + apply inr.
        repeat split;
        [ set (d := d_fri) | set (d := d_gri) | set (d := d_fgri) ];
        refine (transport _ _ d).
        1, 2:
          apply ap, ap;
          refine (ap _ (typed_renaming_respects_types _ _ _ _) @ _);
          apply substitute_rename.
        apply (ap (fun A => [! _ |- _ ≡ _ ; A !])).
        eapply concat. { apply ap, typed_renaming_respects_types. }
        apply substitute_rename.
  Defined.

  (** Given a judgement [ Γ |- J ], and a weakly equal pair [ f, g : Γ' -> Γ ],
   a derivation of [ Γ |- J ] yields derivations of two or possibly three
   judgements over [Γ']:
   - [f^* J];
   - [g^* J];
   - if [J] is an object judgement, the associated equality judgement [f^* J = g^* J]

   The proof of this has to treat all three together, since they are each
   defined mutually with the others.

   We thus wrap them up together in the notion of “weakly equal judgement map”:
   a weakly equal map [ [Γ'|-J'] -> [Γ|-J] ] is a weakly equal pair [f,g] from
   [Γ'] to [Γ], such that [J'] is one of the judgements listed above as induced
   from [J] by the [f, g].

   This then allows the theorem [substitute_equal_derivation] to be stated as:
   given a derivation of [ Γ |- J ] and a weakly equal judgement map
   [ [Γ'|-J'] -> [Γ|-J] ], get a derivation of [ Γ' |- J' ].
*)
  Record weakly_equal_judgement_map
    (T : flat_type_theory Σ) (J' J : judgement Σ)
   := {
     weakly_equal_pair_of_judgement_map
       :> weakly_equal_pair T (context_of_judgement J') (context_of_judgement J)
   ; weakly_equal_judgement_map_hypothetical_part
     : (hypothetical_part J'
         = substitute_hypothetical_judgement
           (left weakly_equal_pair_of_judgement_map)
           (hypothetical_part J))
     + (hypothetical_part J'
         = substitute_hypothetical_judgement
           (right weakly_equal_pair_of_judgement_map)
           (hypothetical_part J))
     + { J_obj : Judgement.is_object (form_of_judgement J)
       & hypothetical_part J'
         = substitute_equal_hypothetical_judgement
           (left weakly_equal_pair_of_judgement_map)
           (right weakly_equal_pair_of_judgement_map)
           (hypothetical_part J)
           J_obj }
     }.

  (** The following two lemmas are definitions are key for the application of weakly equal pairs:
  given a weakly equal pair [(f,g) : Γ' —> Γ], and a context extension [Δ] of [Γ],
  we can extend (f,g) to weakly equal pairs [Γ'.f^*Δ —> Γ.Δ] and [Γ'.g^*Δ —> Γ.Δ]. *)
  Lemma instantiate_context_over_weakly_equal_pair_left
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_equal_pair T
        (Context.instantiate Γ' (substitute_instantiation (left fg) I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    simple refine
      (Build_weakly_equal_pair _ _ _).
    { exact (Substitution.extend Γ Γ' Δ (left fg)). }
    { exact (Substitution.extend Γ Γ' Δ (right fg)). }
    refine (coproduct_rect scope_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (is_weakly_equal fg i)
          as [[j [[e_fij e_gij] e_fg]] | [[d_fi d_gi] d_fgi ]].
      + apply inl.
        exists (coproduct_inj1 scope_is_sum j); repeat split.
        * exact (ap _ e_fij).
        * exact (ap _ e_gij).
        * repeat rewrite coproduct_comp_inj1.
          repeat rewrite substitute_rename.
          destruct e_fg as [e | e];
            [ apply inl | apply inr ]; rewrite e;
            repeat rewrite rename_substitute;
            apply (ap_2back substitute), path_forall; intros x;
            cbn; repeat rewrite coproduct_comp_inj1;
            apply idpath.
      + apply inr.
        repeat split;
          [ set (d := d_fi) | set (d := d_gi) | set (d := d_fgi) ];
          refine (rename_derivation T_sub _ d);
          exists (typed_renaming_to_instantiate_context _ _ _);
          apply eq_by_expressions_hypothetical_judgement; intros j;
          recursive_destruct j; try apply idpath;
          refine (rename_substitute _ _ _ @ _);
          refine (_ @ (substitute_rename _ _ _)^);
          apply (ap_2back substitute), inverse, path_forall; intros j;
          refine (coproduct_comp_inj1 _).
    - intros i. apply inl.
      exists (coproduct_inj2 scope_is_sum i); split.
      + split; unfold Substitution.extend;
        refine (coproduct_comp_inj2 _).
      + apply inl; cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  Lemma instantiate_context_over_weakly_equal_pair_right
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (Δ : raw_context (Metavariable.extend Σ a))
    : weakly_equal_pair T
        (Context.instantiate Γ' (substitute_instantiation (right fg) I) Δ)
        (Context.instantiate Γ I Δ).
  Proof.
    simple refine
      (Build_weakly_equal_pair _ _ _).
    { exact (Substitution.extend Γ Γ' Δ (left fg)). }
    { exact (Substitution.extend Γ Γ' Δ (right fg)). }
    refine (coproduct_rect scope_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (is_weakly_equal fg i)
          as [[j [[e_fij e_gij] e_fg]] | [[d_fi d_gi] d_fgi ]].
      + apply inl.
        exists (coproduct_inj1 scope_is_sum j); repeat split.
        * exact (ap _ e_fij).
        * exact (ap _ e_gij).
        * repeat rewrite coproduct_comp_inj1.
          repeat rewrite substitute_rename.
          destruct e_fg as [e | e];
            [ apply inl | apply inr ]; rewrite e;
            repeat rewrite rename_substitute;
            apply (ap_2back substitute), path_forall; intros x;
            cbn; repeat rewrite coproduct_comp_inj1;
            apply idpath.
      + apply inr.
        repeat split;
          [ set (d := d_fi) | set (d := d_gi) | set (d := d_fgi) ];
          refine (rename_derivation T_sub _ d);
          exists (typed_renaming_to_instantiate_context _ _ _);
          apply eq_by_expressions_hypothetical_judgement; intros j;
          recursive_destruct j; try apply idpath;
          refine (rename_substitute _ _ _ @ _);
          refine (_ @ (substitute_rename _ _ _)^);
          apply (ap_2back substitute), inverse, path_forall; intros j;
          refine (coproduct_comp_inj1 _).
    - intros i. apply inl.
      exists (coproduct_inj2 scope_is_sum i); split.
      + split; unfold Substitution.extend;
        refine (coproduct_comp_inj2 _).
      + apply inr; cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  Local Lemma instantiate_judgement_over_weakly_equal_pair_left
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_equal_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation (left fg) I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_equal_pair_left T_sub fg I _).
    apply inl, inl,
      instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

  Local Lemma instantiate_judgement_over_weakly_equal_pair_right
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _)
    : weakly_equal_judgement_map T
        (Judgement.instantiate Γ' (substitute_instantiation (right fg) I) J)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_equal_pair_right T_sub fg I _).
    apply inl, inr,
      instantiate_hypothetical_judgement_substitute_instantiation.
  Defined.

  (* TODO: check if used in the end; if not, delete! *)
  Local Lemma instantiate_judgement_over_weakly_equal_pair_combined_0
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement _) (J_obj : Judgement.is_object (form_of_judgement J))
    : weakly_equal_judgement_map T
         (combine_judgement
            (Judgement.instantiate Γ' (substitute_instantiation (left fg) I) J)
            (Judgement.instantiate Γ' (substitute_instantiation (right fg) I) J)
            1 J_obj)
        (Judgement.instantiate Γ I J).
  Proof.
    exists (instantiate_context_over_weakly_equal_pair_left T_sub fg I _).
    apply inr; exists J_obj.
    apply eq_by_expressions_hypothetical_judgement.
    intros [ s | | ];
      repeat refine (ap (transport _ _) _);
      apply instantiate_substitute_instantiation.
  Defined.

  (* TODO: upstream within file.  NOTE: keep even if turns out not used, this was a pain in the arse to write and might be useful in future. *)
  Local Definition compose_renaming_weakly_equal_judgement_map
        {T : flat_type_theory Σ}
        {J J' J'' : judgement Σ}
        (r : judgement_renaming J J')
        (fg : weakly_equal_judgement_map T J'' J')
    : weakly_equal_judgement_map T J'' J.
  Proof.
    exists (compose_renaming_weakly_equal_pair r fg).
    destruct fg as [fg fg_J]; simpl.
    destruct fg_J as [ e_fg | [J'_obj e_fg ] ].
    - apply inl.
      destruct e_fg as [ e | e ];
        [ apply inl | apply inr ];
        refine (e @ _);
        refine (_ @ substitute_rename_hypothetical_judgement _ _ _);
        apply ap, inverse, judgement_renaming_hypothetical_part.
    - apply inr.
      destruct r as [r e_r], J' as [Γ' J']; simpl in * |- *.
      destruct e_r.
      exists J'_obj.
      eapply concat. { apply e_fg. }
      apply substitute_equal_rename_hypothetical_judgement.
  Defined.

  (* TODO: upstream within file *)
  Local Definition compose_weakly_equal_pair_renaming
        {T : flat_type_theory Σ} (T_sub : substitutive T)
        {Γ Γ' Γ'' : raw_context Σ}
        (fg : weakly_equal_pair T Γ' Γ)
        (r : typed_renaming Γ' Γ'')
    : weakly_equal_pair T Γ'' Γ.
  Proof.
    set (f := left fg); set (g := right fg).
    apply (Build_weakly_equal_pair (rename r o f) (rename r o g)).
    intros i.
    destruct (is_weakly_equal fg i)
      as [[j [e1 e2]] | [[d_fi d_gi] d_fgi] ].
    - apply inl.
      exists (r j); split.
      + split;
          [ set (e := fst e1) | set (e := snd e1) ];
          (eapply concat; [ apply ap, e | ]);
          apply idpath.
      + destruct e2 as [e2 | e2];
          [ apply inl | apply inr ];
          refine (typed_renaming_respects_types _ _ _ _ @ _);
          refine (ap _ e2 @ _);
          apply rename_substitute.
    - apply inr.
      repeat split;
        [ set (d := d_fi) | set (d := d_gi) | set (d := d_fgi) ];
        refine (rename_derivation T_sub _ d);
        exists r;
        apply eq_by_expressions_hypothetical_judgement; intros s;
        recursive_destruct s; try apply idpath;
        apply rename_substitute.
  Defined.

  (* TODO: upstream within file *)
  Local Definition compose_weakly_equal_judgement_map_renaming
        {T : flat_type_theory Σ} (T_sub : substitutive T)
        {J J' J'' : judgement Σ}
        (fg : weakly_equal_judgement_map T J' J)
        (r : judgement_renaming J' J'')
    : weakly_equal_judgement_map T J'' J.
  Proof.
    exists (compose_weakly_equal_pair_renaming T_sub fg r).
    destruct fg as [fg fg_J]; simpl.
    destruct fg_J as [ e_fg | [J_obj e_fg ] ].
    - apply inl.
      destruct e_fg as [ e | e ];
        [ apply inl | apply inr ];
        refine ((judgement_renaming_hypothetical_part _ _ r)^ @ _);
  (* TODO: try reversing direction of [judgement_renaming_hypothetical_part] *)
        refine (ap _ e @ _);
        apply rename_substitute_hypothetical_judgement.
    - apply inr.
      destruct r as [r e_r], J' as [Γ' J']; simpl in * |- *.
      destruct e_r.
      exists J_obj.
      eapply concat. { apply ap, e_fg. }
      apply rename_substitute_equal_hypothetical_judgement.
  Defined.

  (* TODO: upstream within file? *)
  Local Lemma instantiate_judgement_over_weakly_equal_pair_combined
      {T : flat_type_theory Σ} (T_sub : substitutive T)
      {Γ Γ' : raw_context Σ} (fg : weakly_equal_pair T Γ' Γ)
      {a : arity σ}
      (I : Metavariable.instantiation a Σ Γ.(raw_context_carrier))
      (J : judgement (Metavariable.extend Σ a))
      (J_obj : Judgement.is_object (form_of_judgement J))
    : weakly_equal_judgement_map T
        (Judgement.instantiate Γ'
           (copair_instantiation (substitute_instantiation (left fg) I)
                                 (substitute_instantiation (right fg) I))
           (combine_judgement
               (Judgement.fmap (Metavariable.fmap2 _ Family.inl) J)
               (Judgement.fmap (Metavariable.fmap2 _ Family.inr) J)
            1 J_obj))
        (Judgement.instantiate Γ I J).
  Proof.
    eapply compose_weakly_equal_judgement_map_renaming;
      try apply T_sub.
    { apply (instantiate_judgement_over_weakly_equal_pair_combined_0
                                                    T_sub fg I J J_obj). }
    simple refine (Build_judgement_renaming _ _
                                       (Build_typed_renaming _ _ _ _ _) _).
    - intro i; exact i.
    - intros i.
      eapply concat. 2: { apply inverse, rename_idmap. }
      revert i. apply (coproduct_rect scope_is_sum).
      + intros i.
        eapply concat. { rapply coproduct_comp_inj1. }
        apply inverse; rapply coproduct_comp_inj1.
      + intros i.
        eapply concat. { rapply coproduct_comp_inj2. }
        eapply concat. 2: { apply inverse; rapply coproduct_comp_inj2. }
        apply copair_instantiation_inl.
    - simpl.
      eapply concat. { apply rename_idmap_hypothetical_judgement. }
      eapply concat.
      2: { apply inverse, instantiate_combine_hypothetical_judgement. }
      simple refine (combine_hypothetical_judgement_eq _ _ _ _).
      + apply copair_instantiation_inl_hypothetical_judgement.
      + apply copair_instantiation_inr_hypothetical_judgement.
      + rewrite concat_p1, ap_V.
        eapply concat.
        { apply ap.
          unfold copair_instantiation_inr_hypothetical_judgement,
                 instantiate_fmap2_hypothetical_judgement.
          eapply concat.
          { apply inverse, (ap_compose (Build_hypothetical_judgement _)). }
          apply ap_const. }
        eapply concat.
        { eapply (ap_1back concat), ap.
          unfold copair_instantiation_inl_hypothetical_judgement,
                 instantiate_fmap2_hypothetical_judgement.
          eapply concat.
          { apply inverse, (ap_compose (Build_hypothetical_judgement _)). }
          apply ap_const. }
        apply idpath.
      + eapply concat.
        { unfold copair_instantiation_inl_hypothetical_judgement,
                 instantiate_fmap2_hypothetical_judgement.
          apply inverse.
          refine (transport_compose
                    (fun J => Judgement.is_object (form_of_judgement J))
                    (Build_hypothetical_judgement _) _ _).
        }
        rapply @transport_const.
  Defined.

  Section Flat_Rule_Substitute_Equal_Instantiation.
    (** Analogously to section [Flat_Rule_Substitute_Instantiation],
     the lemmas of this section build up what’s needed for substituting
     flat-rule steps in derivations along weakly equal pairs:

    - given a weakly equal judgement map (f,g) from J' into the conclusion of a flat rule instance I_* R, we get two or three new instantiations: two pulled back instantiations f^*I, g^*I for R, and if R was an object rule, an instantiation (f,g)^*I of the congruence rule of R;

    - the three possible things that J can be are precisely, up to equiv-renaming, the conclusions of these three new rule instances;

    - all of the premises of these new rule instances have weakly equal judgement maps to the premises of the original instance of R.

     The cases for non-flat structural rules amount to showing analogous things for their closure conditions. *)

    Context
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      (J := Judgement.instantiate Γ I (flat_rule_conclusion R))
      {J' : judgement Σ}
      (Γ' := context_of_judgement J')
      (is_obj_R
        := Judgement.is_object (form_of_judgement (flat_rule_conclusion R))).
  (* We can’t include [fg : weakly_equal_judgement_map T J' J] as a section variable here, since the lemmas below need to be able to destruct it and act on the result. *)

  (* Since these lemmas are for internal use only, and their names are getting
  very long, we for once relax our prohibition on abbreviations *)
    Local Definition substeq_flat_rule_pair
        (fg : weakly_equal_judgement_map T J' J)
      : weakly_equal_pair T Γ' Γ.
    Proof.
      simple refine (compose_renaming_weakly_equal_pair _ fg).
      apply typed_renaming_to_instantiate_context.
    Defined.

    Local Definition substeq_flat_rule_rule
        (fg : weakly_equal_judgement_map T J' J)
      : flat_rule Σ.
    Proof.
      destruct fg as [_ [ _ | [ R_obj _]]].
      - exact R.
      - eapply flat_congruence_rule, R_obj.
    Defined.

    Local Definition substeq_flat_rule_instantiation
        (fg : weakly_equal_judgement_map T J' J)
      : Metavariable.instantiation
          (flat_rule_metas (substeq_flat_rule_rule fg)) Σ Γ'.
    Proof.
      set (f' := left (substeq_flat_rule_pair fg)).
      set (g' := right (substeq_flat_rule_pair fg)).
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj ?]]].
      - exact (substitute_instantiation f' I).
      - exact (substitute_instantiation g' I).
      - apply copair_instantiation.
        + exact (substitute_instantiation f' I).
        + exact (substitute_instantiation g' I).
    Defined.

    Local Lemma substeq_flat_rule_conclusion
        (fg : weakly_equal_judgement_map T J' J)
      : judgement_renaming
          (Judgement.instantiate Γ'
            (substeq_flat_rule_instantiation fg)
            (flat_rule_conclusion (substeq_flat_rule_rule fg)))
          J'.
    (* NOTE: and the renaming is in each case an equivalence, though we don’t
       currently need that. *)
    Proof.
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj e_J'_fgJ]]].
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_fJ. }
        eapply concat. { apply rename_substitute_hypothetical_judgement. }
        eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
        apply (ap_1back substitute_hypothetical_judgement), path_forall.
        refine (coproduct_rect scope_is_sum _ _ _).
        2: { refine (empty_rect _ _ _). apply R_univ. }
        intros x1.
        unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
        apply idpath.
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_gJ. }
        eapply concat. { apply rename_substitute_hypothetical_judgement. }
        eapply concat. 2: { apply inverse,
                  instantiate_hypothetical_judgement_substitute_instantiation. }
        apply (ap_1back substitute_hypothetical_judgement), path_forall.
        refine (coproduct_rect scope_is_sum _ _ _).
        2: { refine (empty_rect _ _ _). apply R_univ. }
        intros x1.
        unfold Substitution.extend; repeat rewrite coproduct_comp_inj1.
        apply idpath.
      - simple refine (judgement_renaming_inverse _ _ _ _).
        1: exists (typed_renaming_to_instantiate_context _ _ _).
        2: { apply coproduct_empty_inj1_is_equiv, R_univ. }
        eapply concat. { apply ap, e_J'_fgJ. }
        simpl substeq_flat_rule_instantiation.
        simpl substeq_flat_rule_rule.
        simpl hypothetical_part.
        rewrite instantiate_combine_hypothetical_judgement.
        rewrite rename_combine_hypothetical_judgement.
        refine (ap2 (fun J K
                       => combine_hypothetical_judgement
                            (Build_hypothetical_judgement _ J)
                            (Build_hypothetical_judgement _ K)
                            _ _)
                  _ _).
        (* TODO: refactor using [eq_combbine_hypothetical_judgement]. *)
        + cbn. apply path_forall; intros i.
          eapply concat. 2: { apply inverse, copair_instantiation_inl. }
          eapply concat.
          2: { apply inverse, instantiate_substitute_instantiation. }
          eapply concat. { apply rename_substitute. }
          apply (ap_2back substitute); clear i.
          apply path_forall.
          refine (coproduct_rect scope_is_sum _ _ _).
          2: { apply (empty_rect _ R_univ). }
          intros i. unfold Substitution.extend.
          apply inverse. refine (coproduct_comp_inj1 _).
        + cbn. apply path_forall; intros i.
          eapply concat. 2: { apply inverse, copair_instantiation_inr. }
          eapply concat.
          2: { apply inverse, instantiate_substitute_instantiation. }
          eapply concat. { apply rename_substitute. }
          apply (ap_2back substitute); clear i.
          apply path_forall.
          refine (coproduct_rect scope_is_sum _ _ _).
          2: { apply (empty_rect _ R_univ). }
          intros i. unfold Substitution.extend.
          apply inverse. refine (coproduct_comp_inj1 _).
    Defined.

    Local Lemma substeq_flat_rule_premise
        (fg : weakly_equal_judgement_map T J' J)
        (p : flat_rule_premise (substeq_flat_rule_rule fg))
      : flat_rule_premise R.
    (* for each premise of the new rule used,
       select a premise of the original rule
       to which the new premise will admit a weakly-equal judgement map *)
    Proof.
      destruct fg as [fg [ [ ? | ? ] | [ ? ?]]];
        try (exact p).
      destruct p as [ [ p | p ] | [p _] ];
        exact p.
    Defined.

    Local Lemma substeq_flat_rule_premise_map
        (fg : weakly_equal_judgement_map T J' J)
        (p : flat_rule_premise (substeq_flat_rule_rule fg))
      : weakly_equal_judgement_map T
          (Judgement.instantiate Γ'
                  (substeq_flat_rule_instantiation fg)
                  (flat_rule_premise _ p))
          (Judgement.instantiate Γ I
            (flat_rule_premise _ (substeq_flat_rule_premise _ p))).
    Proof.
      set (fg_orig := fg).
      destruct fg as [fg [ [ e_J'_fJ | e_J'_gJ ] | [ R_obj e_jf]]].
      - (* case: f^* of original rule *)
        apply instantiate_judgement_over_weakly_equal_pair_left, T_sub.
      - (* case: g^* of original rule *)
        apply instantiate_judgement_over_weakly_equal_pair_right, T_sub.
      - (* case: congruence rule *)
        simpl in p. destruct p as [ [p | p] | [p p_obj] ]; simpl.
        + (* left copy of an original premise *)
          rewrite copair_instantiation_inl_judgement.
          refine (instantiate_judgement_over_weakly_equal_pair_left
                    _ (substeq_flat_rule_pair fg_orig) _ _).
          apply T_sub.
        + (* right copy of an original premise *)
          rewrite copair_instantiation_inr_judgement.
          refine (instantiate_judgement_over_weakly_equal_pair_right
                    _ (substeq_flat_rule_pair fg_orig) _ _).
          apply T_sub.
        + (* equality corresponding to an original object premise *)
          refine (instantiate_judgement_over_weakly_equal_pair_combined
                 T_sub (substeq_flat_rule_pair fg_orig) _ _ _).
    Defined.

  End Flat_Rule_Substitute_Equal_Instantiation.

  Theorem substitute_equal_derivation
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} {J'} (fg : weakly_equal_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    (* Sketch proof: should be roughly analogous in organisation to proofs of [rename_derivation], [substitute_derivation] above.

  The sequence of lemmas to handle the flat rule cases should show:

  - given a weakly equal judgement map (f,g) from J' into the conclusion of a flat rule instance I_* R, we get two or three new instantiations: two pulled back instantiations f^*I, g^*I for R, and if R was an object rule, an instantiation (f,g)^*I of the congruence rule of R;

  - the three possible things that J can be are precisely, up to equiv-renaming, the conclusions of these three new rule instances;

  - all of the premises of these new rule instances have weakly equal judgement maps to the premises of the original instance of R.
   *)
    revert J' fg.
    induction d_J as [ | r d_ps IH ].
    { destruct i. } (* hypothesis case impossible, as no hypotheses *)
    intros J' fg.
    destruct r as [ r | r ].
    2: { (* case: instantiation of a flat rule of [T] *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substeq_flat_rule_conclusion _ _ fg)
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (derive_contained_rule _ _ _).
      { destruct fg as [_ [_ | [r_obj _]]].
        - exact r.
        - apply T_cong. exists r. assumption.
      }
      { destruct fg as [fg [? | [r_obj ?]]]; simpl.
        - apply idpath.
        - apply (Family.map_commutes T_cong).
      }
      intros p. apply (IH (substeq_flat_rule_premise _ _ p)).
      refine (substeq_flat_rule_premise_map _ _ _ p); try assumption.
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substeq_flat_rule_conclusion _ _ fg)
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      rename fg into fg_temp; set (fg := fg_temp).
      destruct fg_temp as [fg_map [J'_fg | [r_obj J'_fg]]].
      - simple refine (Closure.deduce' _ _ _).
        { apply inl, inr. exists r.
          exists (context_of_judgement J').
          refine (substeq_flat_rule_instantiation _ fg).
        }
        { apply idpath. }
        intros p. apply (IH (substeq_flat_rule_premise _ fg p)).
        refine (substeq_flat_rule_premise_map _ _ fg p); try assumption.
      - refine (Closure.graft' _ _ _).
        { refine (equality_flat_rules_congruous r_obj _).
          refine (substeq_flat_rule_instantiation _ fg).
        }
        { apply idpath. }
        intros p. apply (IH (substeq_flat_rule_premise _ fg p)).
        refine (substeq_flat_rule_premise_map _ _ fg p); try assumption.
    }
    - (* case: renaming rule *)
      destruct r as [Γ [Γ' [r J]]].
      apply (IH tt).
      exists (compose_renaming_weakly_equal_pair r fg).
      set (e := weakly_equal_judgement_map_hypothetical_part _ _ _ fg).
      (* TODO: make args implicit in […_hypothetical_part] above *)
      (* TODO: consistentise direction of equality in the various judgement maps *)
      destruct e as [[e|e] | [J'_obj e]];
        [ apply inl, inl | apply inl, inr | apply inr; exists J'_obj ];
        refine (e @ _).
      1, 2: apply @substitute_rename_hypothetical_judgement; auto.
      apply @substitute_equal_rename_hypothetical_judgement; auto.
    - (* case: variable rule *)
      destruct r as [Γ i]. cbn in fg.
      destruct J' as [Γ' J'].
      destruct fg as [fg fg_J]; simpl in fg; cbn in fg_J.
      (* There will be nine subcases, according to the three possible cases for the relationship [fg] gives between [J] and [J'], and for what the weakly equal pair [fg] gives at the variable [i].
      To avoid duplicated work between these nine cases, we extract the required cases of the inductive hypothesis before case-splitting. *)
      assert (IH_fΓi : subst_free_derivation T [<>]
                                  [! Γ' |- substitute (left fg) (Γ i) !]).
      { apply (IH tt); exists fg.
        apply inl, inl.
        apply eq_by_eta_hypothetical_judgement, idpath.
      }
      assert (IH_gΓi : subst_free_derivation T [<>]
                                  [! Γ' |- substitute (right fg) (Γ i) !]).
      { apply (IH tt); exists fg.
        apply inl, inr.
        apply eq_by_eta_hypothetical_judgement, idpath.
      }
      assert (IH_fgΓi : subst_free_derivation T [<>]
         [! Γ' |- substitute (left fg) (Γ i) ≡ substitute (right fg) (Γ i) !]).
      { apply (IH tt); exists fg.
        apply inr; exists tt.
        apply eq_by_eta_hypothetical_judgement, idpath.
      }
      clear d_ps IH.
      destruct (is_weakly_equal fg i)
        as [[j [[e_fvar e_gvar] [e_ftype | e_gtype]]] | [[d_fi d_gi] d_fgi ]].
      + (* case: [f i = g i = raw_variable j], [Γ' j = f^* (Γ i) ] *)
        destruct fg_J as [[e|e] | [J'_obj e]];
          (eapply transport; [ eapply ap, inverse, e | ]);
          apply Judgement.canonicalise; simpl.
        * rewrite e_fvar, <- e_ftype.
          apply derive_variable.
          rewrite e_ftype.
          apply IH_fΓi.
        * rewrite e_gvar.
          apply (derive_term_convert Γ' (substitute (left fg) (Γ i)));
            try assumption.
          rewrite <- e_ftype.
          apply derive_variable.
          rewrite e_ftype.
          apply IH_fΓi.
        * rewrite e_fvar, e_gvar.
          apply derive_tmeq_refl.
          rewrite <- e_ftype.
          apply derive_variable.
          rewrite e_ftype.
          exact IH_fΓi.
      + (* case: [f i = g i = raw_variable j], [Γ' j = g^* (Γ i) ] *)
        destruct fg_J as [[e|e] | [J'_obj e]];
          (eapply transport; [ eapply ap, inverse, e | ]);
          apply Judgement.canonicalise; simpl.
        * rewrite e_fvar.
          apply (derive_term_convert Γ' (substitute (right fg) (Γ i)));
            try apply derive_tyeq_sym; try assumption.
          rewrite <- e_gtype.
          apply derive_variable.
          rewrite e_gtype.
          apply IH_gΓi.
        * rewrite e_gvar, <- e_gtype.
          apply derive_variable.
          rewrite e_gtype.
          apply IH_gΓi.
        * rewrite e_fvar, e_gvar.
          apply derive_tmeq_refl.
          apply (derive_term_convert Γ' (substitute (right fg) (Γ i)));
            try apply derive_tyeq_sym; try assumption.
          rewrite <- e_gtype.
          apply derive_variable.
          rewrite e_gtype.
          apply IH_gΓi.
      + (* case: [fg] tells us [ Γ' |- f i = g i : f^* (Γ i) ] *)
        destruct fg_J as [[e|e] | [J'_obj e]];
          cbn in *; destruct e^;
          [ set (d := d_fi) | set (d := d_gi) | set (d := d_fgi) ];
          refine (transport _ _ d);
          apply Judgement.eq_by_eta, idpath.
Defined.

End Equality_Substitution.

Section Subst_Elimination.

  Context `{Funext} {σ : scope_system} {Σ : signature σ}.

  (** \cref{thm:elimination-substitution} *)
  Theorem subst_elimination
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} (d : FlatTypeTheory.derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J.
  Proof.
    induction d as [ [] | r _ d_prems ].
    (* no hypothesis; derivation must conclude with a rule *)
    destruct r as [ [ r_substfree | [ r_subst | r_substeq ] ] | r_from_t ].
    - simple refine (Closure.deduce' _ _ _).
      + exact (inl r_substfree).
      + apply idpath.
      + apply d_prems.
    - destruct r_subst as [Γ [Γ' [J [f f_triv]]]].
      simpl in d_prems |- *.
      simple refine (substitute_derivation _ _ (d_prems None)); try assumption.
      simple refine (Build_weakly_typed_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_typed_context_map _ _ _ f _) | apply idpath].
      intros i.
      destruct (some_or_is_none (f_triv i)) as [[j [e_fi e_Γ'j]]| fi_nontriv].
      * apply inl. exists j; split; assumption.
      * apply inr. exact (d_prems (Some (i;fi_nontriv))).
    - destruct r_substeq as [Γ [Γ' [[f g] [fg_triv [cl J]]]]].
      simpl in d_prems.
      simple refine (substitute_equal_derivation _ _ _ (d_prems None));
        try assumption.
      simple refine (Build_weakly_equal_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_equal_pair _ _ _ f g _) | ].
      2: { apply inr; exists tt; apply idpath. }
      intros i.
      destruct (some_or_is_none (fg_triv i))
        as [[j [[? ?] [? ?]]] | fi_nontriv].
      * apply inl. exists j; repeat split; try apply inl; assumption.
      * set (d_prems_i := fun j => d_prems (Some ((i;fi_nontriv);j)));
          cbn in d_prems_i.
        apply inr; repeat split.
        -- exact (d_prems_i (Some (Some tt))).
        -- exact (d_prems_i (Some None)).
        -- exact (d_prems_i None).
    - simple refine (Closure.deduce' _ _ _).
      + exact (inr (r_from_t)).
      + apply idpath.
      + apply d_prems.
  Defined.

End Subst_Elimination.

(* TODO: it could be nice to give (here or elsewhere) a _counterexample_, showing how over a theory that’s not suitably substitutive/congruous, these results may fail. *)
