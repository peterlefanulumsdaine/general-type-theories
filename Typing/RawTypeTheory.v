Require Import HoTT.HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ScopeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.RawRule.
Require Import Typing.StructuralRule.

(** A _raw type theory_ [raw_type_theory] is just a collection of raw rules.

To any type theory is associated a _closure system_ [RawTypeTheory.closure_system] on judgements, and hence notions of _derivations_ and _derivability_ of judgements.

Raw type theories are a simple notion, sufficient to define derivations of judgements and ensure that they are in some respects well-behaved.  We will later refine these to the notion of a _well-presented_ type theory.
*)

Section RawTypeTheory.

  Context {σ : scope_system}.

  (** A raw type theory is just a family of raw rules. *)
  Definition raw_type_theory (Σ : signature σ) : Type
    := family (raw_rule Σ).

  (** As with closure systems, we will have two notions of maps of raw type theories.

  General maps of raw type theories will send rules of the source theory
  to _derivable_ rules of the target theory. However, developing these requires
  preliminary infrastructure on derivations, for which we will want to make use
  of a notion of _simple maps_ of raw type theories: just a family map between
  their rules, modulo translation under a signature map. *)
  Local Definition simple_map_over
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : raw_type_theory Σ) (T' : raw_type_theory Σ')
    : Type
  := Family.map_over (RawRule.fmap f) T T'.

  Identity Coercion family_map_of_simple_map_over
    : simple_map_over >-> Family.map_over.

  Local Definition simple_map
      {Σ} (T T' : raw_type_theory Σ)
    : Type
  := simple_map_over (Signature.idmap _) T T'.

  Identity Coercion simple_map_over_of_simple_map
    : simple_map >-> simple_map_over.

  Local Lemma simple_map_from_family_map `{Funext}
      {Σ} {T T' : raw_type_theory Σ} (f : Family.map T T')
    : simple_map T T'.
  Proof.
    simple refine (Family.map_transport _ _).
    - apply idmap.
    - apply inverse, path_forall.
      intros i; apply RawRule.fmap_idmap.
    - exact f.
  Defined.

  Local Definition simple_idmap `{Funext}
      {Σ : signature σ} (T : raw_type_theory Σ)
    : simple_map T T.
  Proof.
    apply simple_map_from_family_map, Family.idmap.
  Defined.

  Local Definition simple_compose_over `{Funext}
      {Σ Σ' Σ'': signature σ}
      {f' : Signature.map Σ' Σ''} {f : Signature.map Σ Σ'}
      {T} {T'} {T''}
      (ff' : simple_map_over f' T' T'') (ff : simple_map_over f T T')
    : simple_map_over (Signature.compose f' f) T T''.
  Proof.
    refine (Family.map_transport _ _).
    2: { exact (Family.compose_over ff' ff). }
    apply path_forall; intros r; cbn.
    apply inverse, RawRule.fmap_compose.
  Defined.

  Local Definition simple_compose_over' `{Funext}
      {Σ Σ' Σ'': signature σ}
      {f' : Signature.map Σ' Σ''} {f : Signature.map Σ Σ'}
      {f'' : Signature.map Σ Σ''} (e : f'' = Signature.compose f' f)
      {T} {T'} {T''}
      (ff' : simple_map_over f' T' T'') (ff : simple_map_over f T T')
    : simple_map_over f'' T T''.
  Proof.
    refine (Family.map_transport _ (simple_compose_over ff' ff)).
    apply ap, inverse, e.
  Defined.

  Local Lemma simple_map_from_eq `{Funext}
      {Σ} {T T' : raw_type_theory Σ} (e : T = T')
    : simple_map T T'.
  Proof.
    destruct e. apply simple_idmap.
  Defined.

  (** Translation raw type theories under signature maps *)
  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : raw_type_theory Σ -> raw_type_theory Σ'.
  Proof.
    apply Family.fmap, RawRule.fmap, f.
  Defined.

  Local Definition simple_map_to_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : raw_type_theory Σ)
    : simple_map_over f T (fmap f T).
  Proof.
    apply Family.map_to_fmap.
  Defined.

  (* TODO: consider naming; consider whether would be easier as a family iso instead of an equality. *)
  Local Definition fmap_compose `{Funext}
      {Σ Σ' Σ'' : signature σ}
      (f : Signature.map Σ Σ') (f' : Signature.map Σ' Σ'')
      (T : raw_type_theory Σ)
    : fmap (Signature.compose f' f) T = fmap f' (fmap f T).
  Proof.
    simple refine (Family.eq _ _).
    - apply idpath.
    - intros i; cbn. apply RawRule.fmap_compose.
  Defined.

End RawTypeTheory.

Section ClosureSystem.

  Context {σ : scope_system} `{Funext}.

  (** The closure system associated to a raw type theory [T]:
  consists of structural rules for the signature, plus all instantiations
  of all rules of [T]. *)
  Local Definition closure_system {Σ : signature σ} (T : raw_type_theory Σ)
    : Closure.system (judgement Σ)
    := structural_rule Σ + Family.bind T RawRule.closure_system.

  (** The [closure_system] construction is functorial in simple maps,
  allowing translations of derivations over such maps.

  Below we will see [closure_system] is also functorial in general (Kleisli) maps of raw type theories, but those can’t be defined/developed yet. *)
  Local Definition closure_system_fmap_over_simple
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : raw_type_theory Σ} {T' : raw_type_theory Σ'}
    (ff : simple_map_over f T T')
  : Closure.map_over (Judgement.fmap f)
      (closure_system T)
      (closure_system T').
  Proof.
    unfold closure_system. apply Closure.sum_fmap.
    - apply Closure.map_from_family_map, StructuralRule.fmap.
    - (* TODO: abstract as lemma about [Family.bind]? *)
      apply Closure.map_from_family_map.
      apply Family.Build_map'.
      intros [r I].
      assert (fr
        : Family.map_over (Closure.rule_fmap (Judgement.fmap f))
            (RawRule.closure_system (T r))
            (RawRule.closure_system (T' (ff r)))).
      { apply RawRule.closure_system_fmap'.
        apply inverse, Family.map_over_commutes.
      }
      exists (ff r; (fr I)).
      apply (Family.map_over_commutes fr).
  Defined.

  Local Definition closure_system_fmap_simple
      {Σ : signature σ} {T T' : raw_type_theory Σ} (f : simple_map T T')
    : Closure.map (closure_system T) (closure_system T').
  Proof.
    refine (transport (fun g => Closure.map_over g _ _) _
                      (closure_system_fmap_over_simple f)).
    apply path_forall; intros ?. apply Judgement.fmap_idmap.
  Defined.

End ClosureSystem.

Section Derivations.
  Context {σ : scope_system} `{H_Funext : Funext}.

  (** A derivation of a total judgement in the given raw type theory [T] from
      hypotheses [H], with structural rules included. *)
  Local Definition derivation {Σ : signature σ} (T : raw_type_theory Σ) H
    : judgement Σ -> Type
  := Closure.derivation (closure_system T) H.

  (** Functoriality lemma for derivations under simple maps;
   see [derivation_fmap_over] below for functoriality in general maps. *)
  Local Lemma derivation_fmap_over_simple
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T} {T'} (fT : simple_map_over f T T')
      {H} {H'} (fH : Family.map_over (Judgement.fmap f) H H')
      {J} (D : derivation T H J)
    : derivation T' H' (Judgement.fmap f J).
  Proof.
    refine (Closure.derivation_fmap_over _ fH D).
    apply closure_system_fmap_over_simple, fT.
  Defined.

  Local Lemma derivation_fmap_simple
      {Σ : signature σ}
      {T T' : raw_type_theory Σ} (fT : simple_map T T')
      {H H'} (fH : Family.map H H')
      {J} (D : derivation T H J)
    : derivation T' H' J.
  Proof.
    refine (Closure.derivation_fmap _ fH D).
    apply closure_system_fmap_simple, fT.
  Defined.

  (** Functoriality of derivations in signature maps *)
  Local Lemma derivation_fmap_in_signature
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : raw_type_theory Σ} {H : family (judgement Σ)} {J}
      (D : derivation T H J)
    : derivation
        (fmap f T)
        (Family.fmap (Judgement.fmap f) H)
        (Judgement.fmap f J).
  Proof.
    refine (Closure.derivation_fmap1_over _ D).
    apply closure_system_fmap_over_simple.
    apply simple_map_to_fmap.
  Defined.

  (** Type of derivations of the conclusion of a rule [R] from its premises,
    in raw type theory [T], with given hypotheses.

  I.e. type expressing the proposition that [R] is a derivable rule of [T]. *)
  Local Definition raw_rule_derivation {Σ : signature σ}
        (T : raw_type_theory Σ) (R : raw_rule Σ)
    : Type
  := derivation
       (fmap include_symbol T)
       (raw_rule_premise R)
       (raw_rule_conclusion R).

  (** Any rule of a type theory is derivable over the theory itself. *)
  Local Lemma derive_rule
      {Σ : signature σ} (T : raw_type_theory Σ) (r : T)
    : raw_rule_derivation T (T r).
  Proof.
    unfold raw_rule_derivation.
    simple refine (derive_from_renaming_along_equiv _ _ _).
    2: { apply equiv_inverse, scope_sum_empty_inr. }
    simple refine (Closure.deduce' _ _ _).
    { apply inr. exists r, [::]. apply unit_instantiation. }
    { refine (Judgement.eq_by_expressions _ _).
      - apply (coproduct_rect scope_is_sum).
        { apply empty_rect, scope_is_empty. }
        intros.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        eapply concat. { apply unit_instantiate_expression. }
        apply ap, ap, inverse, eissect.
      - intros; cbn.
        apply unit_instantiate_expression. }
    simpl. intros p.
    simple refine (derive_rename' _ (raw_rule_premise (T r) p) _ _ _).
    { simple refine (Build_typed_renaming _ _ _ _ _).
      + apply scope_sum_empty_inr.
      + intros i.
        eapply concat. { refine (coproduct_comp_inj2 _). }
        apply unit_instantiate_expression.
    }
    { apply eq_by_expressions_hypothetical_judgement; intros s.
      apply unit_instantiate_expression.
    }
    exact (Closure.hypothesis _ _ p).
  Defined.

End Derivations.

(** Interaction between derivations and instantiation of metavariables *)
Section Instantiation.

  Context `{Funext}.
  Context {σ : scope_system} {Σ : signature σ}.

  (** For any raw type theory [T], an an instantiation [I] from a metavariable
  extension [Σ + a] of its signature, there is a closure system map from the
  interpretation of [T] over [Σ + a] to the interpretation of [Σ]: any
  rule of [T] instantiated under [Σ + a] translates back under [I] to an
  instantiation over [Σ] of the same rule of [T],
  modulo some context-reassociation isomorphisms. *)
  Local Definition instantiate_closure_system
      (T : raw_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
    : Closure.map_over (Judgement.instantiate Γ I)
        (closure_system (fmap include_symbol T))
        (closure_system T).
  Proof.
    apply Closure.sum_rect.
    - refine (Closure.compose_over' _ _ _ _ _).
      { apply (StructuralRule.instantiate I). }
      { apply Closure.inl. }
      apply idpath.
    - intros [r I_r].
      refine (Closure.derivation_fmap1 _
        (instantiate_raw_rule_closure_system I (T r) I_r)).
      clear I_r.
      apply Closure.map_from_family_map.
      apply Family.sum_fmap2.
      (* TODO: the following could be a lemma about [Family.bind]? *)
      apply Family.Build_map'.
      intros I_r. exists (r;I_r). apply idpath.
  Defined.

  (** Instantiate derivation [d] with metavariable instantiation [I]. *)
  Local Definition instantiate_derivation
      (T : raw_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      {hyps : family _} (j : judgement (Metavariable.extend Σ a))
      (d : derivation (fmap include_symbol T) hyps j)
    : derivation
        T
        (Family.fmap (Judgement.instantiate _ I) hyps)
        (Judgement.instantiate _ I j).
  Proof.
    apply (Closure.derivation_fmap1_over (instantiate_closure_system _ I)).
    exact d.
  Defined.

End Instantiation.

(* TODO: this section is currently rather disorganised. Would probably benefit from sitting down and thinking about its organisation, with respect to raw type theory maps as something like Kleisli maps. Perhaps compare to organisation in [Auxiliary.Closure]. *)
Section Maps.

  Context `{H_funext : Funext}.
  Context {σ : scope_system}.

  (** A raw type theory map [ff : T -> T'] over a map [f : Σ -> Σ'] of their signatures consists of derivations exhibiting the translation of each rule of [T] as a derivable rule of [T']. *)
  Local Definition map_over
    {Σ Σ': signature σ} (f : Signature.map Σ Σ')
    (T : raw_type_theory Σ) (T' : raw_type_theory Σ')
  := forall R : T,
      raw_rule_derivation T' (RawRule.fmap f (T R)).

  (** Note: being defined as instance the general [map_over] means that [map]
  isn’t quite what one would expect: it includes an extra [RawRule.fmap idmap],
  which is not judgementally the identity.  Is this good or bad? *)
  Local Definition map
    {Σ} (T T' : raw_type_theory Σ)
  := map_over (Signature.idmap Σ) T T'.

  Local Lemma map_over_from_simple_map_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T : raw_type_theory Σ} {T' : raw_type_theory Σ'}
      (ff : simple_map_over f T T')
    : map_over f T T'.
  Proof.
    intros R.
    refine (transport _ (Family.map_over_commutes ff R) _).
    apply derive_rule.
  Defined.

  Local Lemma map_from_simple_map
      {Σ : signature σ} {T T' : raw_type_theory Σ}
      (f : simple_map T T')
    : map T T'.
  Proof.
    apply map_over_from_simple_map_over, f.
  Defined.

  Local Definition idmap
      {Σ : signature σ} (T : raw_type_theory Σ)
    : map T T.
  Proof.
    apply map_from_simple_map, simple_idmap.
  Defined.

  Local Lemma map_from_eq
      {Σ} {T T' : raw_type_theory Σ} (e : T = T')
    : map T T'.
  Proof.
    apply map_from_simple_map, simple_map_from_eq, e.
  Defined.

  Local Lemma map_to_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : raw_type_theory Σ)
    : map_over f T (fmap f T).
  Proof.
    apply map_over_from_simple_map_over, simple_map_to_fmap.
  Defined.

  (** The [closure_system] construction is functorial in maps of raw TT’s.

  This is essentially the core of the “monadicity of derivations”:
  it will allow translation of derivations under such maps,
  and hence will give the Kleisli composition of such maps.  *)
  Local Definition closure_system_fmap_over
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : raw_type_theory Σ} {T' : raw_type_theory Σ'}
    (ff : map_over f T T')
  : Closure.map_over (Judgement.fmap f)
      (closure_system T)
      (closure_system T').
  Proof.
    apply Closure.sum_rect.
    { (* structural rules *)
      apply Closure.map_from_family_map.
      refine (Family.compose_over (Family.inl) _).
      apply StructuralRule.fmap.
    }
    (* Logical rules *)
    intros [r [Γ I]].
    assert (d := @instantiate_derivation _ _ _ _ (Context.fmap f Γ)
                  _ (instantiation_fmap f I) _ _ (ff r)).
    (* From here, want to get goal into a form where it can be obtained
    from [d]. *)
    eapply transport. { apply inverse, Judgement.fmap_instantiate. }
    refine (Closure.derivation_fmap2 _ d).
    refine (transport _ _ (Family.idmap _)).
    simple refine (Family.eq _ _). { apply idpath. }
    intros i. cbn.
    apply inverse, Judgement.fmap_instantiate.
  Defined.

  Local Definition closure_system_fmap
      {Σ : signature σ} {T T' : raw_type_theory Σ} (f : map T T')
    : Closure.map (closure_system T) (closure_system T').
  Proof.
    refine (transport (fun g => Closure.map_over g _ _) _
             (closure_system_fmap_over f)).
    apply path_forall; intros i. apply Judgement.fmap_idmap.
  Defined.

  (** Master functoriality lemma for derivations, though
  [derivation_fmap_simple] should be preferred when applicable. *)
  Local Lemma derivation_fmap_over
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T} {T'} (fT : map_over f T T')
      {H} {H'} (fH : Family.map_over (Judgement.fmap f) H H')
      {J} (D : derivation T H J)
    : derivation T' H' (Judgement.fmap f J).
  Proof.
    refine (Closure.derivation_fmap_over _ fH D).
    apply closure_system_fmap_over, fT.
  Defined.

  Local Definition derivation_fmap1_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T} {T'} (ff : map_over f T T') {H} {J}
    : derivation T H J
    -> derivation T'
         (Family.fmap (Judgement.fmap f) H)
         (Judgement.fmap f J).
  Proof.
    apply Closure.derivation_fmap1_over, closure_system_fmap_over, ff.
  Defined.

  Local Definition derivation_fmap1
      {Σ} {T T' : raw_type_theory Σ} (f : map T T') {H} {J}
    : derivation T H J -> derivation T' H J.
  Proof.
    apply Closure.derivation_fmap1, closure_system_fmap, f.
  Defined.

  Local Definition raw_rule_derivation_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : raw_type_theory Σ} {R : raw_rule Σ} (D : raw_rule_derivation T R)
    : raw_rule_derivation (fmap f T) (RawRule.fmap f R).
  Proof.
    unfold raw_rule_derivation.
    unfold RawRule.fmap. cbn.
    refine (derivation_fmap1_over _ D).
    apply map_over_from_simple_map_over.
    refine (simple_compose_over' _ _ (simple_map_to_fmap _ _)).
    { apply inverse, Signature.id_left. }
    apply simple_map_from_eq.
    eapply concat. 2: { apply fmap_compose. }
    eapply concat. { apply inverse, fmap_compose. }
    apply ap10, ap, inverse, Metavariable.include_symbol_after_map.
  Defined.

  (** Maps of raw TT’s also translate under signature maps *)
  (* TODO: consider naming *)
  Local Definition map_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T T' : raw_type_theory Σ} (g : map T T')
    : map (fmap f T) (fmap f T').
  Proof.
    intros R.
    refine (transport _ _ _). { apply inverse, RawRule.fmap_idmap. }
    apply raw_rule_derivation_fmap.
    refine (transport _ _ _). { apply RawRule.fmap_idmap. }
    apply g.
  Defined.

  Local Lemma map_vs_map_over
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
        (T : raw_type_theory Σ) (T' : raw_type_theory Σ')
    : map (fmap f T) T' <~> map_over f T T'.
  Proof.
    unfold map, map_over.
    apply equiv_functor_forall_id; intros R.
    apply equiv_transport.
    apply RawRule.fmap_idmap.
  Defined.

  Local Definition raw_rule_derivation_fmap_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T} {T'} (ff : map_over f T T')
      {R : raw_rule Σ} (D : raw_rule_derivation T R)
    : raw_rule_derivation T' (RawRule.fmap f R).
  Proof.
    unfold raw_rule_derivation in *.
    refine (derivation_fmap1_over _ D).
    apply map_vs_map_over.
    refine (transport (fun T0 => map T0 _) _ (map_fmap _ _)).
    - eapply concat. 2: { apply fmap_compose. }
      eapply concat. { eapply inverse, fmap_compose. }
      apply ap10, ap. apply Metavariable.include_symbol_after_map.
    - apply (map_vs_map_over _ _ _)^-1, ff.
  Defined.

  Local Definition compose_over
      {Σ Σ' Σ'' : signature σ}
      {f' : Signature.map Σ' Σ''} {f : Signature.map Σ Σ'}
      {T} {T'} {T''} (ff' : map_over f' T' T'') (ff : map_over f T T')
    : map_over (Signature.compose f' f) T T''.
  Proof.
    intros r.
    refine (transport _ _ _). { apply inverse, RawRule.fmap_compose. }
    refine (raw_rule_derivation_fmap_over ff' (ff r)).
  Defined.

  Local Definition compose
      {Σ : signature σ} {T T' T'' : raw_type_theory Σ}
      (f' : map T' T'') (f : map T T')
    : map T T''.
  Proof.
    refine (transport (fun g => map_over g _ _) _ (compose_over f' f)).
    apply Family.id_left.
  Defined.

End Maps.
