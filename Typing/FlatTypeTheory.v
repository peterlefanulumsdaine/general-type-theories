Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Auxiliary.Coproduct.
Require Import Syntax.ShapeSystem.
Require Import Syntax.All.
Require Import Typing.Context.
Require Import Typing.Judgement.
Require Import Typing.FlatRule.
Require Import Typing.StructuralRule.

Section FlatTypeTheory.

  Context {σ : shape_system}.

  (** A flat type theory is just a family of flat rules. *)
  Definition flat_type_theory (Σ : signature σ) : Type
     := family (flat_rule Σ).

  (** The closure system associated to a flat type theory [T]:
  consists of structural rules for the signature, plus all instantiations
  of all rules of [T]. *)
  Local Definition closure_system {Σ : signature σ} (T : flat_type_theory Σ)
    : Closure.system (judgement_total Σ)
    := structural_rule Σ + Family.bind T FlatRule.closure_system.

  (** One can translate flat type theories under signature maps *)
  Local Definition fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
    : flat_type_theory Σ -> flat_type_theory Σ'.
  Proof.
    apply Family.fmap, FlatRule.fmap, f.
  Defined.

  (* TODO: consider naming; consider whether would be easier as an equality. *)
  Local Definition fmap_compose `{Funext}
      {Σ Σ' Σ'' : signature σ}
      (f : Signature.map Σ Σ') (f' : Signature.map Σ' Σ'')
      (T : flat_type_theory Σ)
    : fmap (Signature.compose f' f) T = fmap f' (fmap f T).
  Proof.
    simple refine (Family.eq _ _).
    - apply idpath.
    - intros i; cbn. apply FlatRule.fmap_compose.
  Defined.

End FlatTypeTheory.

Section Derivations.
  Context {σ : shape_system}.
  Context {Σ : signature σ}.

  (** A derivation of a total judgement in the given flat type theory [T] from
      hypotheses [H], with structural rules included. *)
  Local Definition derivation {Σ : signature σ} (T : flat_type_theory Σ) H
    : judgement_total Σ -> Type
  := Closure.derivation (closure_system T) H.

  (** Type of derivations of the conclusion of a rule [R] from its premises,
    in flat type theory [T], with given hypotheses. 

  I.e. type expressing the proposition that [R] is a derivable rule of [T]. *)
  Local Definition flat_rule_derivation
        (T : flat_type_theory Σ) (R : flat_rule Σ)
    : Type
  := derivation 
       (fmap include_symbol T)
       (flat_rule_premise R)
       (flat_rule_conclusion R).

End Derivations.

(** A first few utility derivations, usable for building up others. *)
(* TODO: unify with [UtilityDerivations.v]. *)
Section UtilityDerivations.

  Context {σ : shape_system} `{H_Funext : Funext}.

  (** Commonly-required analogue of [Closure.deduce']. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma deduce_modulo_rename {Σ : signature σ}
      {T : flat_type_theory Σ} {H : family _} {J : judgement_total _}
      (r : closure_system T)
      (e : shape_of_judgement J
          <~> shape_of_judgement (Closure.conclusion (closure_system T r)))
      (e_J : Judgement.rename (Closure.conclusion (closure_system T r)) e
             = J)
      (D : forall p : Closure.premises (closure_system T r),
          derivation T H (Closure.premises _ p))
    : derivation T H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (Closure.conclusion (closure_system T r)). exact (_;e).
    - apply e_J.
    - intros [].
      exact (Closure.deduce _ _ r D).
  Defined.

  (** Commonly-required analogue of [Closure.deduce'], similar to [deduce_modulo_rename] above. *)
  (* TODO: after some use, consider whether this would be more convenient with
   the equivalence given in the other direction. *)
  Lemma hypothesis_modulo_rename {Σ : signature σ}
      {T : flat_type_theory Σ} {H : family (judgement_total _)}
      {J : judgement_total _}
      (h : H)
      (e : shape_of_judgement J <~> shape_of_judgement (H h))
      (e_J : Judgement.rename (H h) e = J)
    : derivation T H J.
  Proof.
    simple refine (Closure.deduce' _ _ _).
    - apply inl, StructuralRule.rename.
      exists (H h). exact (_;e).
    - apply e_J.
    - intros [].
      exact (Closure.hypothesis _ _ h).
  Defined.

  (** Any rule of a type theory is derivable over the theory itself. *)
  (* TODO: consider name *)
  Lemma flat_type_theory_derive_rule `{Funext}
      {Σ : signature σ} (T : flat_type_theory Σ) (r : T)
    : flat_rule_derivation T (T r).
  Proof.
    unfold flat_rule_derivation.
    simple refine (deduce_modulo_rename _ _ _ _).
    - apply inr. exists r, [::]. apply unit_instantiation.
    - apply shape_sum_empty_inr.
    - cbn.
      (* TODO: the following should be much simpler, using
      [Judgement.unit_instantiate], but the typing of [Judgement.rename]
      (in particular, the way it uses [shape_of_judgement]) makes it
      very difficult.  This would work better if judgements were
      parametrised over shapes before judgement forms? *)
      set (J := (T.(family_element) r).(flat_rule_conclusion)).
      clearbody J. destruct J as [ [ | hjf ] J].
      + (* context judgement *)
        apply (ap (Build_judgement_total _)).
        destruct J as [ Γ [] ].
        apply (ap (fun Γ => Build_judgement Γ _)).
        apply (ap (Build_raw_context _)).
        apply path_forall; intros i.
        cbn. eapply concat.
        { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, unit_instantiate_expression. }
        eapply concat. { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply (ap (fun f => rename f _)).
        apply path_forall; intros j.
        refine (coproduct_comp_inj2 _).
      + (* hypothetical judgement *)
        apply Judgement.eq_by_expressions; intros i.
        * (* context part *)
        cbn. eapply concat.
        { apply ap. refine (coproduct_comp_inj2 _). }
        eapply concat. { apply ap, unit_instantiate_expression. }
        eapply concat. { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply (ap (fun f => rename f _)).
        apply path_forall; intros j.
        refine (coproduct_comp_inj2 _).          
        * cbn.
        eapply concat. { apply ap, unit_instantiate_expression. }
        eapply concat. { apply inverse, rename_comp. }
        eapply concat. 2: { apply rename_idmap. }
        apply (ap (fun f => rename f _)).
        apply path_forall; intros j.
        refine (coproduct_comp_inj2 _).
    - cbn. intros p.
      simple refine (hypothesis_modulo_rename _ _ _).
      + exact p.
      + apply equiv_inverse, shape_sum_empty_inr.
      + cbn. apply inverse, Judgement.unit_instantiate.
  Defined.

End UtilityDerivations.

(** Interaction between derivations and instantiation of metavariables *) 
Section Instantiation.

  Context `{Funext}.
  Context {σ : shape_system} {Σ : signature σ}.

  (** Given a flat rule [R] over a signature [Σ], an arity [a] specifying a
  metavariable extension, and an instantiation [I] of [a] in [Σ] over some
  context [Γ],

  any instance of [R] over the extended signature [extend Σ a] gets translated
  under [I] into an instance of [R] over [Σ], modulo renaming. 

  Note: this can’t be in [Typing.FlatRule], since it uses the structural rules,
  specifically the rule for renaming along shape isomorphisms.  Morally perhaps
  that should be seen as more primitive than the other structural rules, and be
  baked into the notion of derivations earlier, as e.g. “closure systems on a
  groupoid”.  (Indeed, if the shape system is univalent then this rule _will_
  come for free.)
  *)
  Local Definition instantiate_flat_rule_closure_system
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      (r : flat_rule Σ)
    : Closure.map_over
        (Judgement.instantiate Γ I)
        (FlatRule.closure_system (FlatRule.fmap include_symbol r))
        (structural_rule Σ + FlatRule.closure_system r).
  Proof.
    intros [Δ J].
    (* The derivation essentially consists of the instance
     [(Context.instantiate _ I Δ
     ; instantiate_instantiation I J)]
     of the same flat rule, wrapped in renamings along [shape_assoc].
     *)
    simple refine (Closure.deduce' _ _ _).
    { apply inl. apply StructuralRule.rename. cbn.
      set (j := Judgement.instantiate Γ I
         (Closure.conclusion
            (FlatRule.closure_system (FlatRule.fmap include_symbol r) (Δ;J)))).
      exists (Judgement.rename j (shape_assoc _ _ _)^-1).
      refine (_ ; shape_assoc _ _ _).
    }
    { apply Judgement.rename_inverse. }
    intros []; cbn.
    simple refine (Closure.deduce' _ _ _).
    { apply inr. 
      exists (Context.instantiate _ I Δ).
      exact (instantiate_instantiation I J).
    }
    { apply Judgement.instantiate_instantiate. }
    cbn. intros p.
    simple refine (Closure.deduce' _ _ _).
    { apply inl, StructuralRule.rename. cbn.
      exists
        (Judgement.instantiate Γ I
          (Judgement.instantiate Δ J
            (fmap_judgement_total
              (Metavariable.fmap1 include_symbol _)
              (flat_rule_premise r p)))).
      refine (_ ; (equiv_inverse (shape_assoc _ _ _))).
    }
    { apply inverse, Judgement.instantiate_instantiate. }
    intros [].
    simple refine (Closure.hypothesis' _ _).
    { exact p. }
    { apply idpath. }
  Defined.

  (** For any flat type theory [T], an an instantiation [I] from a metavariable 
  extension [Σ + a] of its signature, there is a closure system map from the
  interpretation of [T] over [Σ + a] to the interpretation of [Σ]: any
  rule of [T] instantiated under [Σ + a] translates back under [I] to an
  instantiation over [Σ] of the same rule of [T]. *)
  Local Definition instantiate_closure_system
      (T : flat_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
    : Closure.map_over (Judgement.instantiate Γ I)
        (closure_system (fmap include_symbol T)) 
        (closure_system T).
  Proof.
    apply Closure.sum_rect.
    - apply Closure.map_from_family_map.
      refine (Family.compose_over (Family.inl) (StructuralRule.instantiate _)).
    - intros [r I_r].
      refine (Closure.fmap_derivation _
        (instantiate_flat_rule_closure_system I (T r) I_r)).
      clear I_r.
      apply Closure.map_from_family_map.
      apply (Family.fmap_of_sum (Family.idmap _)).
      (* TODO: the following could be a lemma about [Family.bind]? *)
      apply Family.Build_map'.
      intros I_r. exists (r;I_r). apply idpath.
  Defined.

  (** Instantiate derivation [d] with metavariable instantiation [I]. *)
  Local Definition instantiate_derivation
      (T : flat_type_theory Σ)
      {Γ : raw_context Σ} {a : arity σ} (I : Metavariable.instantiation a Σ Γ)
      {hyps : family _} (j : judgement_total (Metavariable.extend Σ a))
      (d : derivation (fmap include_symbol T) hyps j)
    : derivation T (Family.fmap (Judgement.instantiate _ I) hyps)
                   (Judgement.instantiate _ I j).
  Proof.
    simple refine (Closure.fmap_derivation_over _ d).
    apply instantiate_closure_system.
  Defined.

End Instantiation.

(* TODO: this section is currently rather disorganised. Would probably benefit from sitting down and thinking about its organisation, with respect to flat type theory maps as something like Kleisli maps. *)
Section Maps.

  Context `{H_funext : Funext}.
  Context {σ : shape_system}.

  (** A flat type theory map [ff : T -> T'] over a map [f : Σ -> Σ'] of their signatures consists of derivations exhibiting the translation of each rule of [T] as a derivable rule of [T']. *)
  Local Definition map_over
    {Σ Σ': signature σ} (f : Signature.map Σ Σ')
    (T : flat_type_theory Σ) (T' : flat_type_theory Σ')
  := forall R : T,
      flat_rule_derivation T' (FlatRule.fmap f (T R)).

  (** Note: being defined as instance the general [map_over] means that [map]
  is not quite what one would expect: it includes an extra [FlatRule.fmap idmap],
  which is not judgementally the identity.  Is this good or bad? *)
  Local Definition map
    {Σ} (T T' : flat_type_theory Σ)
  := map_over (Signature.idmap Σ) T T'.

  Local Lemma map_over_from_family_map_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
      (ff : Family.map_over (FlatRule.fmap f) T T')
    : map_over f T T'.
  Proof.
    intros R.
    refine (transport _ (Family.map_over_commutes ff R) _).
    apply flat_type_theory_derive_rule.
  Defined.

  Local Lemma map_from_family_map
      {Σ} {T T' : flat_type_theory Σ} (f : Family.map T T')
    : map T T'.
  Proof.
    intros R.
    refine (transport _ _ _).
    - eapply concat. { apply inverse, FlatRule.fmap_idmap. }
      apply ap, (Family.map_commutes f).
    - apply flat_type_theory_derive_rule.
  Defined.

  Local Definition idmap
      {Σ : signature σ} (T : flat_type_theory Σ)
    : map T T.
  Proof.
    apply map_from_family_map, Family.idmap.
  Defined.

  Local Lemma map_from_eq
      {Σ} {T T' : flat_type_theory Σ} (e : T = T')
    : map T T'.
  Proof.
    destruct e. apply idmap.
  Defined.

  Local Lemma map_to_fmap
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      (T : flat_type_theory Σ)
    : map_over f T (fmap f T).
  Proof.
    apply map_over_from_family_map_over.
    apply Family.map_to_fmap.
  Defined.

  (** The [closure_system] construction is functorial in maps of flat TT’s.
   This is what will allow translation of derivations under such maps. *)
  Local Definition fmap_closure_system_over
    {Σ Σ': signature σ} {f : Signature.map Σ Σ'}
    {T : flat_type_theory Σ} {T' : flat_type_theory Σ'}
    (ff : map_over f T T')
  : Closure.map_over (fmap_judgement_total f)
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
    intros [r [Γ I]]. cbn.
    (* From here, want to get goal into a form where it can be obtained
     by [instantiate_derivation]. *)
    eapply transport. { apply inverse, Judgement.fmap_instantiate. }
    eapply (transport (fun H => derivation _ H _)).
    { apply inverse.
      eapply concat. { apply inverse, Family.fmap_compose. }
      eapply concat.
      { refine (ap10 _ _). apply ap, path_forall; intros i.
        apply Judgement.fmap_instantiate. }
      apply Family.fmap_compose.
    }
    apply instantiate_derivation.
    apply ff.
  Defined.

  Local Definition fmap_closure_system
      {Σ : signature σ} {T T' : flat_type_theory Σ} (f : map T T')
    : Closure.map (closure_system T) (closure_system T').
  Proof.
    refine (transport (fun g => Closure.map_over g _ _) _
             (fmap_closure_system_over f)).
    apply path_forall; intros i. apply fmap_judgement_total_idmap.
  Defined.

  (* TODO: consider naming of this and following lemma. *)
  Local Lemma fmap_derivation
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : flat_type_theory Σ} {H : family (judgement_total Σ)} {J}
      (D : derivation T H J)
    : derivation
        (fmap f T)
        (Family.fmap (fmap_judgement_total f) H)
        (fmap_judgement_total f J).
  Proof.
    refine (Closure.fmap_derivation_over _ D).
    apply fmap_closure_system_over.
    apply map_to_fmap.
  Defined.

  (* TODO: consider naming; of this and preceding lemma! *)
  Local Definition fmap_derivation_in_theory
      {Σ} {T T' : flat_type_theory Σ} (f : map T T') {H} {J}
    : derivation T H J -> derivation T' H J.
  Proof.
    apply Closure.fmap_derivation, fmap_closure_system, f.
  Defined.

  Local Definition fmap_derivation_in_theory_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T} {T'} (ff : map_over f T T') {H} {J}
    : derivation T H J
    -> derivation T'
         (Family.fmap (fmap_judgement_total f) H)
         (fmap_judgement_total f J).
  Proof.
    apply Closure.fmap_derivation_over, fmap_closure_system_over, ff.
  Defined.

  Local Definition fmap_flat_rule_derivation
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T : flat_type_theory Σ} {R : flat_rule Σ} (D : flat_rule_derivation T R)
    : flat_rule_derivation (fmap f T) (FlatRule.fmap f R).
  Proof.
    unfold flat_rule_derivation.
    unfold FlatRule.fmap. cbn.
    refine (fmap_derivation_in_theory _ _).
    2: { exact (fmap_derivation _ D). }
    apply map_from_eq.
    eapply concat. 2: { apply fmap_compose. }
    eapply concat. { apply inverse, fmap_compose. } 
    apply ap10, ap, inverse, Metavariable.include_symbol_after_map.
  Defined.


  (** Maps of flat TT’s also translate under signature maps *)
  (* TODO: consider naming! *)
  Local Definition fmap_map
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
      {T T' : flat_type_theory Σ} (g : map T T')
    : map (fmap f T) (fmap f T').
  Proof.
    intros R.
    refine (transport _ _ _). { apply inverse, FlatRule.fmap_idmap. }
    apply fmap_flat_rule_derivation. 
    refine (transport _ _ _). { apply FlatRule.fmap_idmap. }
    apply g.
  Defined.

  Local Lemma map_vs_map_over
        {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
        (T : flat_type_theory Σ) (T' : flat_type_theory Σ')
    : map (fmap f T) T' <~> map_over f T T'.
  Proof.
    unfold map, map_over.
    apply equiv_functor_forall_id; intros R.
    apply equiv_transport.
    apply FlatRule.fmap_idmap.
  Defined.

  Local Definition fmap_flat_rule_derivation_over
      {Σ Σ' : signature σ} {f : Signature.map Σ Σ'}
      {T} {T'} (ff : map_over f T T')
      {R : flat_rule Σ} (D : flat_rule_derivation T R)
    : flat_rule_derivation T' (FlatRule.fmap f R).
  Proof.
    unfold flat_rule_derivation in *.
    refine (fmap_derivation_in_theory_over _ D).
    apply map_vs_map_over.
    refine (transport (fun T0 => map T0 _) _ (fmap_map _ _)).
    - eapply concat. 2: { apply fmap_compose. }
      eapply concat. { eapply inverse, fmap_compose. }
      apply ap10, ap. apply Metavariable.include_symbol_after_map.
    - apply (map_vs_map_over _ _ _)^-1, ff.
  Defined.

  Local Definition compose_over
      {Σ Σ' Σ'' : signature σ} {f' : Signature.map Σ' Σ''} {f : Signature.map Σ Σ'}
      {T : flat_type_theory Σ} {T' : flat_type_theory Σ'} {T'' : flat_type_theory Σ''}
      (ff' : map_over f' T' T'') (ff : map_over f T T')
    : map_over (Signature.compose f' f) T T''.
  Proof.
    intros r.
    refine (transport _ _ _). { apply inverse, FlatRule.fmap_compose. }
    refine (fmap_flat_rule_derivation_over ff' (ff r)).
  Defined.

  Local Definition compose
      {Σ : signature σ} {T T' T'' : flat_type_theory Σ}
      (f' : map T' T'') (f : map T T')
    : map T T''.
  Proof.
    refine (transport (fun g => map_over g _ _) _ (compose_over f' f)).
    apply Family.id_left.
  Defined.


End Maps.
