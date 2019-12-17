Require Import HoTT.
Require Import Syntax.ShapeSystem.
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
only require renaming along _equivalences_ of shapes. *)

(* TODO: perhaps restrict the renaming rule (either in general, or just
in [structural_rule_without_subst]) to just the case of equivalences,
so that the results of this file really do show that general renaming is
admissible. *)

Section Subst_Free_Derivations.

  Context {σ : shape_system}.

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

  (* TODO: we will probably need to generalise various lemmas from ordinary to
  subst-free derivations.  Hopefully this can be done, as far as possible, by
  proving the original lemmas in type-class based ways, which will then apply
  automatically to subst-free derivations. *)

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
    := is_empty (shape_of_judgement (flat_rule_conclusion R)).

  Definition substitutive (T : flat_type_theory Σ)
    := forall r : T, in_universal_form (T r).

  (* TODO: upstream to [FlatRule]? *)
  Definition flat_congruence_rule
      (R : flat_rule Σ)
      (R_obj : Judgement.is_object (form_of_judgement (flat_rule_conclusion R)))
    : flat_rule Σ.
  Proof.
    assert (inl : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inl. }
    assert (inr : (Signature.map
       (Metavariable.extend Σ (flat_rule_metas R))
       (Metavariable.extend Σ (flat_rule_metas R + flat_rule_metas R)))).
    { apply Metavariable.fmap2, Family.inr. }
    exists (flat_rule_metas R + flat_rule_metas R).
    - (* premises *)
      refine (_ + _ + _).
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inl.
      + refine (Family.fmap _ (flat_rule_premise R)).
        apply Judgement.fmap, inr.
      + exists {p : flat_rule_premise R
                    & Judgement.is_object
                        (form_of_judgement (flat_rule_premise R p))}.
        intros [p p_obj].
        set (J := flat_rule_premise R p).
        fold J in p_obj.
        exists (Context.fmap inl (context_of_judgement J)).
        exists (form_equality (Judgement.class_of (form_of_judgement J))).
        intros [ s_bdry | | ].        
        * (* boundary slot *)
          apply (Expression.fmap inl).
          refine (transport (fun cl => raw_expression _ cl _) _ _).
          2: { exact (J (the_boundary_slot
                          (boundary_slot_from_object_boundary_slot s_bdry))). }
          eapply concat. { apply Family.map_commutes. }
          eapply (Family.map_commutes boundary_slot_from_object_boundary_slot).
        * (* LHS slot *)
          apply (Expression.fmap inl).
          exact (Judgement.head J p_obj).
        * (* RHS slot *)
          apply (Expression.fmap inr).
          exact (Judgement.head J p_obj).
    - (* conclusion *)
      set (J := flat_rule_conclusion R).
      exists (Context.fmap inl (context_of_judgement J)).
      exists (form_equality (Judgement.class_of (form_of_judgement J))).
      intros [ s_bdry | | ].        
      * (* boundary slot *)
        apply (Expression.fmap inl).
        refine (transport (fun cl => raw_expression _ cl _) _ _).
        2: { exact (J (the_boundary_slot
                         (boundary_slot_from_object_boundary_slot s_bdry))). }
        eapply concat. { apply Family.map_commutes. }
        eapply (Family.map_commutes boundary_slot_from_object_boundary_slot).
      * (* LHS slot *)
        apply (Expression.fmap inl).
        exact (Judgement.head J R_obj).
      * (* RHS slot *)
        apply (Expression.fmap inr).
        exact (Judgement.head J R_obj).
  Defined.

  Local Definition congruous (T : flat_type_theory Σ) (T_sub : substitutive T)
    : Type.
  (* Note: the unused [T_sub] parameter is deliberate; see discussion below. *)
  Proof.
    refine
      (forall (r:T)
              (r_obj : Judgement.is_object
                         (form_of_judgement (flat_rule_conclusion (T r)))), _).
    admit.
  (*
  Choosing the right definition here is rather subtle!  Roughly, we want something like “for each object rule of T, its congruence rule is derivable over T”, or perhaps “admissible over T”, or simply “…in T”.

  “…in T” is simplest, but stronger than ideal; there are alternative formulations of the congruence rules someone might take, and the theorems we give should work for theories using any of them.

  “…derivable over T” seems nicest, but our primary reading of “derivable” for flat rules, as “derivable in its metavariable extension”, is problematic, since giving such derivations will almost always need the subst rules (both subst-apply and subst-eq!), to use the metavariables applied to arguments other than their variables.

  “…admissible over T”: would only allow substitution-eq elimination in _closed_ derivations, which is weaker than should hold; and also this is weaker than we want;

  How about: “every _instance_ or R is subst-free derivable over T”?  This is a slightly ad hoc notion of derivability; compared to the standard notion, it’s roughly what you get from ordinary derivability, but assuming instantiability of derivations.  But it’s not very well-behaved, eg not preserved by translation of T to extended signatures.

  So I guess: we want to say something like “derivable in the metavariable extension, using subst and subst-apply _only at the premises_”. That’s stable under translation, and is also how one shows it in practice.  But how can one say it??

  First idea: just add all substitution instances of the rule’s premises as extra premises.  Problem: we don’t want to add all instances, just the well-typed ones (or perhaps weakly-well-typed), so we need to somehow add _rules_ not premises.

  Second idea: go back to the old idea of converting premises to rules, i.e. if the rule had a premise like [ x:A |- B(x) type ], then in the metavariable extension we add two extra rules
[ |- a:A // |- B(a) type ] and [ |- a = a' : A // |- B(a) = B(a') type ].

  This… should work??  When we instantiate such a derivation at an instantiation [I], we will have to do something clever when those rules are used.  We’ll need to know, roughly, that for the instantiation of each premise of the rule, not just that premise itself but _all further well-typed substitutions/subst-equals_ of it hold?  Something like that.  It feels… right, it feels like it should be right, since that’ll hold in the inductive proof of subst-equal elimination, but the organisation requires some thought.

  But still, this second idea is rather complicated.

  Third idea, less general but simpler for now: just say we actually have _the_ congruence rules for all the flat rules. *)
  Admitted. (* [congruous]: actually needs further thought! *)

End Flat_Conditions.

Section Judgement_Renamings.
(** A lot of results can be concisely formulated in terms of maps/renamings of
judgements.  A map/renaming of judgements from [Γ' |- J'] to [Γ |- J] is just
a context map/renaming [f] from [Γ'] to [J], such that [J' = f^*J].

(Categorically, these are exactly maps in the total category of judgements,
viewed as a discrete fibration over contexts.)

This section gives judgement renamings; section [Weakly_Typed_Maps] below gives
the analogue for (weakly) typed context maps. *)

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

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

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

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
      refine (coproduct_rect shape_is_sum _ _ _).
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
    intro r; recursive_destruct r; apply shape_is_empty.
  Defined.

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
      { cbn. apply (ap (Build_judgement _)). 
        set (e := judgement_renaming_hypothetical_part _ _ f).
        eapply concat. 2: { apply e. }
        apply (ap (Build_hypothetical_judgement _)). 
        apply path_forall.
        intros s; recursive_destruct s; try apply idpath.
        apply typed_renaming_respects_types.        
      }
      intros p; set (p_keep := p); recursive_destruct p. cbn.
      apply (IH p_keep).
      set (f0 := typed_renaming_of_judgement_renaming _ _ f).
      cbn in f0. exists f0.
      apply (ap (Build_hypothetical_judgement _)). 
      apply path_forall.
      intros s; recursive_destruct s.
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

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Local Definition weakly_typed 
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ) (f : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j) * (Δ j = substitute f (Γ i)) }
    + subst_free_derivation T (Family.empty _)
                            [! Δ |- f i ; substitute f (Γ i) !].

  Local Record weakly_typed_context_map
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
    - intros i. exact (Expression.rename f (g i)).
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
        apply (ap (Build_hypothetical_judgement _)).
        (* TODO: abstract the above as [hypothetical_judgement_eq_by_expressions?
           It’s used so often. *)
        apply path_forall.
        intros j; recursive_destruct j.
        * apply rename_substitute.
        * apply idpath.
  Defined.

  Local Lemma compose_renaming_weakly_typed_context_map
        {T : flat_type_theory Σ} (T_sub : substitutive T)
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
    refine (coproduct_rect shape_is_sum _ _ _).
    - intros i.
      unfold Substitution.extend; cbn.
      repeat rewrite coproduct_comp_inj1.
        destruct (weakly_typed_context_map_is_weakly_typed _ _ _ f i)
          as [[j [e1 e2]] | d_fi].
      + apply inl.
        exists (coproduct_inj1 shape_is_sum j); split.
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
        apply (ap (Build_hypothetical_judgement _)).
        apply path_forall; intros j; recursive_destruct j.
        * eapply concat. { apply rename_substitute. }
          eapply concat. 2: { apply inverse, substitute_rename. }
          apply (ap_2back substitute), path_forall; intros j.
          apply inverse. refine (coproduct_comp_inj1 _).
        * apply idpath.
    - intros i. apply inl.
      exists (coproduct_inj2 shape_is_sum i); split.
      + unfold Substitution.extend; cbn.
        refine (coproduct_comp_inj2 _).
      + cbn.
        repeat rewrite coproduct_comp_inj2.
        apply instantiate_substitute_instantiation.
  Defined.

  (** Analogous to [judgement_renaming] *)
  Local Record weakly_typed_judgement_map
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

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

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
      (* TODO: composition of a w *)
      simple refine (compose_renaming_weakly_typed_context_map _ _ f).
      { assumption. }
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
      refine (coproduct_rect shape_is_sum _ _ _).
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
        (substitute_flat_rule_instantiation_conclusion T_sub _ _ f) 
        _ _).
      { apply T_sub. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation T_sub _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
    }
    (* case: structural rules *)
    destruct r as [ [ r | r ] | r ].
    3: { (* case: equality rule; so again, an instantiation of a flat rule *)
      destruct r as [r I].
      simple refine (derive_rename' _ _
        (substitute_flat_rule_instantiation_conclusion T_sub _ _ f) 
        _ _).
      { apply equality_flat_rules_in_universal_form. }
      { apply inverse, judgement_renaming_hypothetical_part. }
      simple refine (Closure.deduce' _ _ _).
      { apply inl, inr. exists r.
        exists (context_of_judgement J').
        refine (substitute_flat_rule_instantiation_instantiation T_sub _ f).
      }
      { apply idpath. }
      intros p. apply (IH p).
      refine (substitute_flat_rule_instantiation_premise _ _ f p).
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_renaming_weakly_typed_context_map T_sub g f).
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
      apply (ap (Build_hypothetical_judgement _)). 
      apply path_forall.
      intros s; recursive_destruct s.
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

The idea of this is that it generalises judgemental equality so as to be closed under extending/weakening a pair [f, g] by types either of the form [f^*A] or [g^*A], without any derivability check for [A] (which would be required for the extensions to be still judgementally equal).  Such extensions arise when going under binders in premises of rules.

Since the resulting maps may not be weakly-typed context maps, so not automatically applicable for [substitute_derivation], we also strengthen the statement to conclude additionally that [ Γ |- f^*a : f^*A ] and [ Γ |- g^*a : g^*A ]. *)

  Context {σ : shape_system} {Σ : signature σ}.

  Local Definition weakly_equal
      (T : flat_type_theory Σ)
      {Δ Γ : raw_context Σ}
      (f g : raw_context_map Σ Δ Γ)
    : Type
  := forall i : Γ,
      { j : Δ & (f i = raw_variable j) 
                * ((Δ j = substitute f (Γ i))
                  + (Δ j = substitute g (Γ i))) }
    + subst_free_derivation T (Family.empty _)
          [! Δ |- f i ≡ g i ; substitute f (Γ i) !].

  Local Record weakly_equal_pair
      (T : flat_type_theory Σ)
      (Δ Γ : raw_context Σ)
  := {
    left : raw_context_map Σ Δ Γ
  ; right : raw_context_map Σ Δ Γ
  ; is_weakly_equal : weakly_equal T left right
  }.

  Arguments left {_ _ _} _.
  Arguments right {_ _ _} _.

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
  Local Record weakly_equal_judgement_map
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

  
  Theorem substitute_equal_derivation
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T T_sub)
      {J} {J'} (f : weakly_equal_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    (* Sketch proof: should be analogous in organisation to proofs of [rename_derivation], [substitute_derivation] above, including a roughly analogous series of lemmas to handle the flat rule cases. *)
  Admitted. (* [substitute_equal_derivation]: substantial amount of work to do. *)

End Equality_Substitution.

Section Subst_Elimination.

  Context `{Funext} {σ : shape_system} {Σ : signature σ}.

  Theorem subst_elimination
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T T_sub)
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
    - destruct r_subst as [Γ [Γ' [f J]]].
      simpl in d_prems |- *.
      simple refine (substitute_derivation _ _ (d_prems None)); try assumption.
      simple refine (Build_weakly_typed_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_typed_context_map _ _ _ f _) | ].
      + intros i. apply inr.
        exact (d_prems (Some i)).          
      + apply idpath.
    - destruct r_substeq as [Γ [Γ' [f [g [cl J]]]]].
      simpl in d_prems.
      simple refine (substitute_equal_derivation _ _ _ (d_prems None));
        try assumption.
      simple refine (Build_weakly_equal_judgement_map _ _ _ _ _);
        [ simple refine (Build_weakly_equal_pair _ _ _ f g _) | ].
        * intros i. apply inr.
          exact (d_prems (Some (inr i))).
        * apply inr.
          exists tt; apply idpath.
    - simple refine (Closure.deduce' _ _ _).
      + exact (inr (r_from_t)).
      + apply idpath.
      + apply d_prems.
  Defined.

End Subst_Elimination.

(* TODO: it could be nice to give (here or elsewhere) a _counterexample_, showing how over a theory that’s not suitably substitutive/congruous, these results may fail. *)