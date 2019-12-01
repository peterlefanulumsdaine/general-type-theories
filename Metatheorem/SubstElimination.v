Require Import HoTT.
Require Import Syntax.ShapeSystem.
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

  Context {σ} {Σ : signature σ}.

  Definition closure_system_without_subst (T : flat_type_theory Σ)
    := structural_rule_without_subst Σ + Family.bind T FlatRule.closure_system.

  Definition subst_free_derivation (T : flat_type_theory Σ)
    := derivation (closure_system_without_subst T).

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

  (* TODO: once defined, upstream to [FlatRule]? *)
  Definition flat_congruence_rule (R : flat_rule Σ) : flat_rule Σ.
  Proof.
  Admitted. (* [flat_congruence_rule]: shouldn’t be too much work to define *)

  Definition congruous (T : flat_type_theory Σ) : Type.
  Admitted. (* [congruous]: requires definition upstream of _admissibiility_
             of a rule over a closure system/flat type theory. *)

End Flat_Conditions.

Section Judgement_Maps.
(** A lot of results can be concisely formulated in terms of maps/renamings of
judgements.  A map/renaming of judgements from [Γ' |- J'] to [Γ |- J] is just
a context map/renaming [f] from [Γ'] to [J], such that [J' = f^*J].

(Categorically, these are exactly maps in the total category of judgements,
viewed as a discrete fibration over contexts.

We also introduce an auxiliary notion of _weakly typed_ context maps:
maps which at each component look either like a well-typed context map, or
like a typed renaming. *)

  Context {σ : shape_system} {Σ : signature σ}.

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
 
  Local Record judgement_renaming (J J' : judgement Σ)
  := {
    typed_renaming_of_judgement_renaming
      :> typed_renaming (context_of_judgement J) (context_of_judgement J')
  ; judgement_renaming_hypothetical_part
      : rename_hypothetical_judgement
          typed_renaming_of_judgement_renaming 
          (hypothetical_part J)
        = hypothetical_part J'
  }.

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

  (* TODO: not sure if this is really the right definition to be using.  Experiment! *)
  Local Record closure_rule_renaming (R' R : Closure.rule (judgement Σ))
  := {
    closure_rule_renaming_conclusion
      : judgement_renaming (conclusion R') (conclusion R)
  ; closure_rule_renaming_premise
      : forall p : premises R',
        { q : premises R & judgement_renaming (premises R' p) (premises R q) }
    }.

End Judgement_Maps.

Section Rename_Derivations.
(** The goal of this section is [rename_derivation]:
given a judgement-renaming from [J] to [J'],
and a derivation [d] of [J],
we can rename throughout [d] to get a derivation of [J']. 

The proof of [rename_derivation] is by direct structural induction on
derivations; the rest of this section is devoted to the lemmas needed in
the cases of that induction. *)

  Context {σ : shape_system} {Σ : signature σ}.

  Section Flat_Rule_Instantiation_Renaming.
    (* The lemmas of this section build up what’s needed for renaming
     flat-rule steps in derivations: 

     given an instance of a flat rule in universal form,
     and a judgement-renaming into its conclusion,
     get a renamed instance, whose conclusion is renaming-equivalent to the
     renaming we want to derive, and each of whose premises has a
     judgement-renaming to some premise of the original rule.

     Cases for non-flat structural rules: should be done by analogous
     claim for their closure conditions.
    *)

    Context {R : flat_rule Σ} (R_univ : in_universal_form R)
      {Γ : raw_context Σ}
      (I : Metavariable.instantiation (flat_rule_metas R) Σ Γ)
      {J' : judgement Σ}
      (f : judgement_renaming
             (Judgement.instantiate Γ I (flat_rule_conclusion R))
             J')
      (Γ' := context_of_judgement J').

    (* TODO: consider naming of following lemma sequence *)
    Local Definition rename_flat_rule_instantiation_renaming
      : typed_renaming Γ Γ'.
    Proof.
    Admitted. (* [rename_flat_rule_instantiation_renaming]: hopefully self-contained *)

    Local Definition rename_flat_rule_instantiation_instantiation
      : Metavariable.instantiation (flat_rule_metas R) Σ Γ'.
    Proof.
    Admitted. (* [rename_flat_rule_instantiation_instantiation]: hopefully simple once  [reame_flat_rule_instantiation_renaming] done *)

    Local Lemma rename_flat_rule_instantiation_conclusion
      : judgement_renaming
          (Judgement.instantiate Γ'
            (rename_flat_rule_instantiation_instantiation)
            (flat_rule_conclusion R))
          J'.
    (* NOTE: and moreover this judgement_renaming is an equivalence, which may
    be needed if we restrict the renaming structural rule to equivalences. *)
    Proof.
    Admitted. (* [rename_flat_rule_instantiation_conclusion]: hopefully straightforward following aobve dependencies *)

    Local Lemma rename_flat_rule_instantiation_premise
          (p : flat_rule_premise R)
      : judgement_renaming
          (Judgement.instantiate Γ I (flat_rule_premise R p))
          (Judgement.instantiate Γ' rename_flat_rule_instantiation_instantiation
                                                       (flat_rule_premise R p)).
    Proof.
    Admitted. (* [rename_flat_rule_instantiation_premise]: hopefully straightforward following aove dependencies *)

  End Flat_Rule_Instantiation_Renaming.

  Context `{Funext}.

  (* TODO: upstream? *)
  Lemma equality_flat_rules_in_universal_form
    : forall r : @equality_flat_rule σ,
      in_universal_form (equality_flat_rule r).
  Proof.
    intro r; recursive_destruct r; apply shape_is_empty.
  Defined.

  (* TODO: upstream to [Context] *)
  Lemma comp_respects_types 
     {Γ Γ' Γ'': raw_context Σ}
     {f : Γ' -> Γ''} {g : Γ -> Γ'}
     (H_f : respects_types Γ' Γ'' f)
     (H_g : respects_types Γ Γ' g)
    : respects_types Γ Γ'' (f o g).
  Proof.
    intros i.
    eapply concat. { apply H_f. }
    eapply concat. { apply ap, H_g. }
    apply rename_rename.
  Defined.

  (* TODO: upstream to [Context] *)
  Definition compose_typed_renaming
     {Γ Γ' Γ'': raw_context Σ}
     (f : typed_renaming Γ' Γ'') (g : typed_renaming Γ Γ')
    : typed_renaming Γ Γ''.
  Proof.
    exists (f o g).
    apply comp_respects_types; apply typed_renaming_respects_types.
  Defined.

  (* TODO: upstream to [Judgement] *)
  Definition rename_rename_hypothetical_judgement
      {γ γ' γ'' : σ} (f : γ -> γ') (g : γ' -> γ'')
      (J : hypothetical_judgement Σ γ)
    : rename_hypothetical_judgement g
        (rename_hypothetical_judgement f J)
    = rename_hypothetical_judgement (g o f) J.
  Proof.
    apply (ap (Build_hypothetical_judgement _)).
    apply path_forall; intros i; apply rename_rename.
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
        refine (rename_flat_rule_instantiation_instantiation _ _ f). 
        apply T_sub. }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ _ f p).
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
        refine (rename_flat_rule_instantiation_instantiation _ _ f). 
        apply equality_flat_rules_in_universal_form. }
      { apply idpath. }
      intros p. apply (IH p).
      refine (rename_flat_rule_instantiation_premise _ _ f p).
    }
    - (* case: renaming rule *)
      cbn in r.
      destruct r as [Γ [Γ' [g J]]].
      apply (IH tt).
      exists (compose_typed_renaming f g).
      eapply concat. 2: { apply (judgement_renaming_hypothetical_part _ _ f). }
      apply inverse, @rename_rename_hypothetical_judgement.
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

Section Substitute_Derivations.

  Context {σ : shape_system} {Σ : signature σ}.

  Definition substitute_derivation
      {T : flat_type_theory Σ} (T_sub : substitutive T) 
      {J} {J'} (f : weakly_typed_judgement_map T J' J)
      (d_J : subst_free_derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J'.
  Proof.
    (* This proof should be closely analogous to [rename_derivation].
    One extra ingredient: will require weakening/extending weakly-typed context
    maps, for going under binders in premises of rules; this will be defined in
    terms of [rename_derivation]. *)
  Admitted. (* [sustitute_derivation]: major proposition, probably requires a fair bit of work. *)

  (* Note: both [rename_derivation] and [sustitute_derivation] have analogues for derivations with hypotheses. For now we give just the versions for closed derivations.  *)
End Substitute_Derivations.

Section Subst_Elimination.

  Context {σ : shape_system} {Σ : signature σ}.

  Theorem subst_elimination
      {T : flat_type_theory Σ}
      (T_sub : substitutive T) (T_cong : congruous T)
      {J} (d : FlatTypeTheory.derivation T (Family.empty _) J)
    : subst_free_derivation T (Family.empty _) J.
  Proof.
    (* Direct structural induction on derivations;
     most rules are translated to the same rule in the subst-free setting;
     [subst_apply] is handled by [substitute_derivation]; 
     [subst_equal] should be handled be [subst_equal_derivation] (to be given!). *)
  Admitted. (* Theorem [subst_elimination]: major goal, depends on a lot of upstream work *)

End Subst_Elimination.

(* TODO: it could be nice to give (here or elsewhere) a _counterexample_, showing how over a theory that’s not suitably substitutive/congruous, these results may fail. *)