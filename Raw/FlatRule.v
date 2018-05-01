Require Import HoTT.
Require Import Auxiliary.Coproduct.
Require Import Auxiliary.Family.
Require Import Auxiliary.Closure.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.SyntaxLemmas.

Section FlatRule.

  Context {σ : shape_system}.
  Context (Σ : signature σ).

  (* TODO: Is it right that we allow arbitrary judgements, or should we allow
     only _hypothetical_ judgements? *)
  Record flat_rule
  :=
    { flat_rule_metas : arity _
    ; flat_rule_premises :
        family (judgement_total (Metavariable.extend Σ flat_rule_metas))
    ; flat_rule_conclusion :
        (judgement_total (Metavariable.extend Σ flat_rule_metas))
    }.

  Local Definition closure_system (R : flat_rule)
    : Closure.system (judgement_total Σ).
  Proof.
    exists { Γ : raw_context Σ &
                 Metavariable.instantiation (flat_rule_metas R) Σ Γ }.
    intros [Γ I].
    split.
    - (* premises *)
      refine (Family.fmap _ (flat_rule_premises R)).
      apply (Metavariable.instantiate_judgement _ I).
    - apply (Metavariable.instantiate_judgement _ I).
      apply (flat_rule_conclusion R).
  Defined.

End FlatRule.

Arguments closure_system {_ _} _.

Section SignatureMaps.

  Context `{Funext} {σ : shape_system}.

  Local Definition fmap
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_rule Σ -> flat_rule Σ'.
  Proof.
    intros R.
    exists (flat_rule_metas _ R).
    - refine (Family.fmap _ (flat_rule_premises _ R)).
      apply fmap_judgement_total.
      apply Metavariable.fmap1, f.
    - refine (fmap_judgement_total _ (flat_rule_conclusion _ R)).
      apply Metavariable.fmap1, f.
  Defined.

  Local Definition fmap_closure_system 
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
        (R : flat_rule Σ)
    : Family.map_over (Closure.fmap (fmap_judgement_total f))
        (closure_system R)
        (closure_system (fmap f R)).
  Proof.
    apply Family.Build_map'.
    intros [Γ I_R].
    exists (Context.fmap f Γ ; fmap_instantiation f I_R).
    apply Closure.rule_eq.
    - simple refine (Family.eq _ _). { apply idpath. }
      cbn. intros i. apply inverse, fmap_instantiate_judgement.
    - cbn. apply inverse, fmap_instantiate_judgement.
  Defined.

End SignatureMaps.

Section Instantiations.

  Context {σ : shape_system} {Σ : signature σ}.

  (* TODO: upstream to [ShapeSystems]? *)
  (* TODO: perhaps make into equivalence? *)
  Definition shape_assoc (γ δ κ : shape_carrier σ)
    : shape_sum γ (shape_sum δ κ) <~> shape_sum (shape_sum γ δ) κ.
  Proof.
    simple refine (equiv_adjointify _ _ _ _); unfold Sect.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj1 shape_is_sum), (coproduct_inj2 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - repeat apply (coproduct_rect shape_is_sum); intros i.
      + repeat apply (coproduct_inj1 shape_is_sum); exact i.
      + apply (coproduct_inj2 shape_is_sum), (coproduct_inj1 shape_is_sum), i.
      + repeat apply (coproduct_inj2 shape_is_sum); exact i.
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
    - unfold Sect. repeat apply (coproduct_rect shape_is_sum); intros i.
      + eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj1 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj1 _). }
        eapply concat. { refine (coproduct_comp_inj1 _). }
        refine (coproduct_comp_inj2 _).
      + eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap. refine (coproduct_comp_inj2 _). }
        refine (coproduct_comp_inj2 _).
  Defined.

  (* TODO: upstream to [Raw.Syntax.Metavariable]? *)
  Definition instantiate_instantiation
      (Γ : raw_context _) {a} (I : Metavariable.instantiation a Σ Γ)
      (Δ : raw_context _) {b}
      (J : Metavariable.instantiation b (Metavariable.extend Σ a) Δ)
    : Metavariable.instantiation b Σ (Metavariable.instantiate_context Γ I Δ).
  Proof.
    intros i.
    refine (rename _ (Metavariable.instantiate_expression I (J i))).
    apply shape_assoc.
  Defined.

  (** Given a flat rule [R] over a signature [Σ], an arity [a] specifying a
   metavariable extension, and an instantiation [I] of [a] in [Σ] over some context [Γ],

   any instance of [R] over the extended signature [extend Σ a] gets translated
   under [I] into an instance of [R] over [Σ]. *)
  Local Definition instantiate
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : flat_rule Σ)
    : Family.map_over
        (Closure.fmap (Metavariable.instantiate_judgement Γ I))
        (closure_system (fmap include_symbol r))
        (closure_system r).
  Proof.
    apply Build_map'. 
    intros [Δ J].
    exists (Metavariable.instantiate_context _ I Δ ;
            instantiate_instantiation _ I _ J).
    apply Closure.rule_eq.
    - admit. (* should be like the conclusion below, but inside [Family.eq.] *)
    - admit. (* Some lemma about instantiating twice *)
  Admitted.

End Instantiations.